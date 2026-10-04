"""Observe emitted scalar guards separately from the actual assembly runs."""
import json,re,subprocess,collections
import native_variable_cancel as fixture
from native_zero_trip import function_body
from native_memory_layout_sequence_paths import printer_for_gcc

def instrument(dump):
    source=printer_for_gcc(dump).split('\nint guard_original_main(void)',1)[0]
    for slot,name in enumerate(fixture.NAMES):
        body=function_body(source,name)
        changed,count=re.subn(r'if \((\$[xy] != 0)\)',
            lambda match:f'if ((guard_entries[{slot}]++, {match[1]}))',body)
        assert count==1,(name,count)
        pattern=r'\$[0-9]+ = [^;]+;' if slot==3 else r'return [^;]+;'
        def mark(match):
            statement=match[0]
            counter='fallback' if '/' in statement else 'fast'
            if '$x' not in statement:return statement
            return f'guard_{counter}[{slot}]++; '+statement
        changed=re.sub(pattern,mark,changed)
        source=source.replace(body,changed,1)
    return 'int guard_fast[4],guard_fallback[4],guard_entries[4];\n'+source

def main(services=None):
    report=json.loads((fixture.WORK/'report.json').read_text());assert report['status']=='passed'
    configurations={}
    for name,row in report['configurations'].items():
        work=fixture.WORK/name;dump=work/'variable-cancel.light.c'
        assert fixture.compiler.sha(dump)==row['clight_sha256']
        service=(services or {'unified':fixture.compiler,'conditioned':fixture.conditioned})[name]
        assert service.check_build()['compiler_sha256']==row['compiler_sha256']
        source=instrument(dump.read_text());calls=[];counts=collections.Counter()
        for args in fixture.inputs():
            which,x,y=args;branch=fixture.expected_branch(args);counts[branch]+=1
            arguments=str(x) if which==2 else f'{x},{y}'
            calls.append(f'guard_fast[{which}]=guard_fallback[{which}]=guard_entries[{which}]=0;'
                f'if({fixture.NAMES[which]}({arguments})!={fixture.model(args)} || '
                f'guard_fast[{which}]!={int(branch=="fast")} || '
                f'guard_fallback[{which}]!={int(branch=="fallback")} || '
                f'guard_entries[{which}]!={int(branch!="unreached")}) return 1;')
        source+='\nint main(void){\n'+'\n'.join(calls)+'\nreturn 0;}\n'
        path=work/'branch-diagnostic.c';path.write_text(source)
        subprocess.run(['gcc','-O0','-fwrapv','-Wno-builtin-declaration-mismatch',str(path),
            '-o',str(work/'branch-diagnostic')],check=True,capture_output=True)
        output=subprocess.check_output([str(work/'branch-diagnostic')],text=True)
        (work/'branch-output.txt').write_text(output)
        configurations[name]={'compiler_sha256':row['compiler_sha256'],'actual_calls':len(calls),
            'branches':dict(counts),'diagnostic_source_sha256':fixture.compiler.sha(path),
            'diagnostic_output_sha256':fixture.compiler.sha(work/'branch-output.txt')}
        print(name,dict(counts),flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'configurations':configurations,'scope':'GCC execution of instrumented emitted Clight; actual assembly checked separately'},indent=2)+'\n')

if __name__=='__main__':main()
