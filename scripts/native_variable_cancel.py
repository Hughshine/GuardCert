"""Exercise variable multiplication/division rewrites in complete C programs."""
import json,subprocess,os
from pathlib import Path
import native_guardcert as compiler
import native_affine_nest_condition_search as conditioned
from native_zero_trip import function_body

ROOT=compiler.ROOT;WORK=ROOT/'build/native-variable-cancel'
SOURCE=ROOT/'examples/native_variable_cancel.c'
VALUES=[-2**31,-2**31+1,-46341,-46340,-2,-1,0,1,2,46340,46341,1073741823,1073741824,2**31-1]
NAMES=['guarded_mul_div','guarded_mul_div_context','guarded_square_div','unreachable_division']
word=compiler.deep.word

def inputs():
    return [(which,x,y) for which in [0,1,3] for x in VALUES for y in VALUES]+[(2,x,0) for x in VALUES]

def model(row):
    which,x,y=row
    if which==3:return 0 if y==0 else 76
    if which==2:
        if x==0:return 75
        y=x
    else:
        if y==0:return 73
        if y==-1 and x==-2**31:return 74
    product=word(x*y);quotient=abs(product)//abs(y)*(-1 if (product<0)!=(y<0) else 1)
    return word((quotient+17)*3) if which==1 else quotient

def expected_branch(row):
    which,x,y=row
    if which==3 or y==0 and which!=2 or which==2 and x==0:
        return 'unreached'
    if which!=2 and y==-1 and x==-2**31:
        return 'unreached'
    y=x if which==2 else y
    return 'fast' if -2**31<=x*y<2**31 else 'fallback'

def generate():
    source=WORK/'variable-cancel.c'
    text=SOURCE.read_text().split('int main(void)',1)[0]+'int main(void){\n'
    for which,x,y in inputs():
        args=str(x) if which==2 else f'{x},{y}'
        text+=f'printf("{which} {x} {y} %d\\n",{NAMES[which]}({args}));\n'
    source.write_text(text+'return 0;}\n');return source

def main():
    WORK.mkdir(parents=True,exist_ok=True);source=generate()
    expected=''.join(' '.join(map(str,[*row,model(row)]))+'\n' for row in inputs())
    compiler.rectangular.common.checked_reference(source,WORK,expected)
    configurations={}
    witnesses=[[0,2**31-1,2],[0,-2**31,2],[2,46341,0]]
    assert all(model(row)!=row[1] and expected_branch(row)=='fallback' for row in witnesses)
    for name,service in [('unified',compiler),('conditioned',conditioned)]:
        stamp=service.check_build();work=WORK/name;work.mkdir(exist_ok=True)
        env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
        env['GUARDCERT_AFFINE_MODE']='disabled'
        with (work/'compile.log').open('w') as log:
            result=subprocess.run([str(service.COMPILER),'-conf',str(service.COMPILER.parent/'compcert.ini'),
                '-stdlib',str(service.COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'program.s'),str(source)],
                cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
        assert result.returncode==0,(work/'compile.log').read_text()[-3000:]
        subprocess.run(['gcc','-no-pie',str(work/'program.s'),'-o',str(work/'program')],check=True,capture_output=True)
        actual=subprocess.check_output([str(work/'program')],text=True,timeout=120)
        assert actual==expected,name
        (work/'output.txt').write_text(actual)
        dump=work/'variable-cancel.light.c'
        for fn in NAMES:assert 'long long' in function_body(dump.read_text(),fn),fn
        configurations[name]={'actual_calls':len(inputs()),'compiler_sha256':stamp['compiler_sha256'],
            'assembly_sha256':compiler.sha(work/'program.s'),'clight_sha256':compiler.sha(dump),
            'output_sha256':compiler.sha(work/'output.txt'),'all_word_boundary_outputs_match':True}
        print(name,len(inputs()),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','source_sha256':compiler.sha(source),
        'configurations':configurations,'unsafe_unguarded_rewrite_counterexamples':witnesses,'scope':'actual assembly from two independently audited whole-program entries'},indent=2)+'\n')

if __name__=='__main__':main()
