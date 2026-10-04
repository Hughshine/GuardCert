from pathlib import Path
import itertools,hashlib,json
import native_memory_affine_alias as common
ROOT=common.ROOT
SIZE=4096;CENTER=2048
NAMES=['signed_copy1','signed_copy2','signed_chain2','signed_mixed2','signed_copy3','signed_undefined2']
DIMENSIONS=[1,2,2,2,3,2]
SOURCE=ROOT/'examples/native_memory_signed_multiple_pointers.c'
WORK=ROOT/'build/native-memory-signed-multiple-pointers'
word=common.word

def locations(kind):
 if kind==0:return {'p':(0,CENTER),'q':(1,CENTER)}
 return {'p':(0,CENTER),'q':(0,CENTER+{1:256,2:0,3:1,4:16}[kind])}

def points(args):
 which,kind,start,n,m,s,u,v,alpha,beta=args
 return itertools.product(range(start,n),*([range(max(0,m))] if DIMENSIONS[which]>=2 else []),*([range(max(0,s))] if DIMENSIONS[which]>=3 else []))

def accesses(which,coordinate,u,v):
 i=coordinate[0];j=coordinate[1] if len(coordinate)>1 else 0;k=coordinate[2] if len(coordinate)>2 else 0
 index=i if which==0 else 16*i+4*j+k if which==4 else 16*i+j
 result=[('p',index+u),('q',index+v)]
 if which==2:result.append(('q',index+v+1))
 return result

def output_model(args,reverse=False,fission=False):
 which,kind,start,n,m,s,u,v,alpha,beta=args
 arrays=[[3*x+1 for x in range(SIZE)],[5*x+7 for x in range(SIZE)]]
 binding=locations(kind) if kind!=5 else None
 def get(pointer,index):
  assert binding is not None,args
  block,base=binding[pointer];assert 0<=base+index<SIZE,(args,pointer,index)
  return arrays[block][base+index]
 def put(pointer,index,value):
  assert binding is not None,args
  block,base=binding[pointer];assert 0<=base+index<SIZE,(args,pointer,index)
  arrays[block][base+index]=word(value)
 order=[(coordinate,site) for coordinate in points(args) for site in range(2 if which in [2,3] else 1)]
 if reverse:order.sort(key=lambda item:(-item[0][0],*item[0][1:],item[1]))
 if fission:order.sort(key=lambda item:(item[1],*item[0]))
 for coordinate,site in order:
  i=coordinate[0];j=coordinate[1] if len(coordinate)>1 else 0;k=coordinate[2] if len(coordinate)>2 else 0
  index=i if which==0 else 16*i+4*j+k if which==4 else 16*i+j
  if site==0:put('p',index+u,get('q',index+v)*alpha+beta*i+j+k)
  elif which==2:put('q',index+v+1,get('p',index+u)+get('q',index+v+1)*beta+i-j)
  else:put('q',index+v,get('p',index+u)+i-j)
 final_i=max(start,n);final_j=max(0,m) if DIMENSIONS[which]>=2 and start<n else 77
 final_k=max(0,s) if DIMENSIONS[which]>=3 and start<n and m>0 else 91
 return ' '.join(map(str,list(args)+[final_i,final_j,final_k]+[value for array in arrays for value in array]))+'\n'

def full_inputs():
 result=[]
 shapes=[(-2,3,2,2),(-16,1,1,1),(0,3,2,2),(1,3,1,1),(-3,-1,2,2),(-65,-64,1,1),(0,64,2,2)]
 for which in range(len(NAMES)):
  for start,n,m,s in shapes:
   for u,v in [(-1,1),(-3,-1),(0,0)]:
    for kind in range(5):result.append((which,kind,start,n,m,s,u,v,-7,11))
  for u,v in [(-64,1),(64,1),(1,64)]:result.append((which,0,-2,3,2,2,u,v,-7,11))
  for kind in [0,3]:result.append((which,kind,-2,3,2,2,-1,1,-2147483648,2147483647))
  for start,n in [(2,2),(3,2),(-2147483648,-2147483648),(2147483647,2147483647)]:result.append((which,5,start,n,2,2,-2147483648,-2147483648,2147483647,-2147483648))
  if DIMENSIONS[which]>=2:result.append((which,5,-1,3,0,2,-2147483648,-2147483648,2147483647,-2147483648))
  if DIMENSIONS[which]>=3:result.append((which,5,-1,3,2,0,-2147483648,-2147483648,2147483647,-2147483648))
 return list(dict.fromkeys(result))

def literal(x):return '(-2147483647-1)' if x==-2147483648 else str(x)

def generate():
 source='#include <stdio.h>\nint signed_out_i,signed_out_j,signed_out_k;\n'
 for which,fn in enumerate(NAMES):
  dimensions=DIMENSIONS[which];index='i' if which==0 else '16*i+4*j+k' if which==4 else '16*i+j'
  suffix='beta*i'+('+j' if dimensions>=2 else '')+('+k' if dimensions>=3 else '')
  first=f'p[{index}+u]=q[{index}+v]*alpha+{suffix};'
  if which==2:first+=f'q[{index}+v+1]=p[{index}+u]+q[{index}+v+1]*beta+i-j;'
  if which==3:first+=f'q[{index}+v]=p[{index}+u]+i-j;'
  prefix=''
  if which==5:
   prefix='int local_u,local_v,local_alpha; if(start<n && m>0) {local_u=u;local_v=v;local_alpha=alpha;} '
   first=first.replace('+u]', '+local_u]').replace('+v]','+local_v]').replace('*alpha','*local_alpha')
  loop='for(;i<n;i++) '+('for(j=0;j<m;j++) ' if dimensions>=2 else '')+('for(k=0;k<s;k++) ' if dimensions>=3 else '')+'{'+first+'}'
  source+=f'void {fn}(int *p,int *q,int start,int n,int m,int s,int u,int v,int alpha,int beta) {{int i=start,j=77,k=91; {prefix}{loop} signed_out_i=i;signed_out_j=j;signed_out_k=k;}}\n'
 source+='void signed_case(int which,int kind,int start,int n,int m,int s,int u,int v,int alpha,int beta) {int a[4096],b[4096],x;int *p,*q; for(x=0;x<4096;x++){a[x]=3*x+1;b[x]=5*x+7;} p=a+2048;q=b+2048; if(kind==1)q=p+256;if(kind==2)q=p;if(kind==3)q=p+1;if(kind==4)q=p+16;if(kind==5){p=0;q=0;}\n'
 for which,fn in enumerate(NAMES):source+=f'if(which=={which}){fn}(p,q,start,n,m,s,u,v,alpha,beta);\n'
 source+='printf("%d %d %d %d %d %d %d %d %d %d %d %d %d",which,kind,start,n,m,s,u,v,alpha,beta,signed_out_i,signed_out_j,signed_out_k);for(x=0;x<4096;x++)printf(" %d",a[x]);for(x=0;x<4096;x++)printf(" %d",b[x]);printf("\\n");}\nint main(void){\n'
 for args in full_inputs():source+='signed_case('+','.join(literal(x) for x in args)+');\n'
 source+='return 0;}\n';SOURCE.write_text(source)

def witnesses():
 reverse=(0,3,-2,3,1,1,0,0,-7,11)
 fission=(2,0,-2,3,2,1,0,0,-7,11)
 assert output_model(reverse)!=output_model(reverse,reverse=True)
 assert output_model(fission)!=output_model(fission,fission=True)
 return {'overlapping_pointer_reversal_changes_result':list(reverse),'distinct_pointer_fission_breaks_true_dependence':list(fission)}



def observed_functions(dump):
 import native_memory_signed_windows as parser
 old_names,old_dims=parser.NAMES,parser.DIMENSIONS
 try:
  parser.NAMES,parser.DIMENSIONS=NAMES,DIMENSIONS
  return parser.observed_functions(dump)
 finally:parser.NAMES,parser.DIMENSIONS=old_names,old_dims

def templates():
 from native_memory_pointer import loop_template
 result={f'direct-identity-{d}':loop_template(d) for d in [1,2,3]}
 result.update({f'direct-interchange-{d}':loop_template(d,[1,0]+list(range(2,d))) for d in [2,3]})
 result.update({'schedule-identity-2':'(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
  'schedule-interchange-2':'(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
  'schedule-fission-2':'(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
  'schedule-reverse-1':'(schedule ((negative-coordinate 0) ordinal) ((reflect 0)))',
  'tile-2-3':'(tile 2 3)','tile-17-13':'(tile 17 13)',
  'invalid-coordinate':'(schedule ((coordinate 8) ordinal) ())'})
 return result

def main():
 import argparse
 parser=argparse.ArgumentParser();parser.add_argument('--reference-only',action='store_true');parser.add_argument('--cases');args=parser.parse_args()
 inputs=full_inputs();counterexamples=witnesses()
 reference=common.checked_reference(SOURCE,WORK,''.join(output_model(row) for row in inputs))
 if args.reference_only:print('Signed multiple-pointer source fixture:',len(inputs),'complete GCC outputs agree with the word model');return
 stamp=common.check_build();proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text());assert proof['memory_signed_multiple_pointer_csem_asm_proved']
 proposals=templates();options=[(name,syntax,{}) for name,syntax in proposals.items()]
 options += [(name,proposals['schedule-interchange-2'],extra) for name,extra in [('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
 selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options};assert selected<={name for name,_,_ in options};configurations={}
 for name,syntax,extra in options:
  if name not in selected:continue
  dump,clight_bytes,assembly_bytes=common.compile_run(SOURCE,WORK/name,'(interval (per-axis '+syntax+'))',extra,reference)
  found=observed_functions(dump)
  if extra or name=='invalid-coordinate':assert not found,(name,found)
  else:
   dimensions=1 if name=='schedule-reverse-1' else 2 if name.startswith(('schedule','tile-')) else int(name[-1])
   expected={fn for fn,d in zip(NAMES,DIMENSIONS) if d==dimensions}
   assert expected<=set(found),(name,expected,found)
   assert all(found[fn]['whole_source_region'] for fn in expected),(name,found)
  configurations[name]={'guarded_functions':found,'actual_calls':len(inputs),'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':clight_bytes,'assembly_bytes':assembly_bytes}
  print(name,{fn:row['count_caps'] for fn,row in found.items()},flush=True)
 report={'status':'passed','compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,'full_configuration_suite':not bool(args.cases),'dependence_witnesses':counterexamples,'scope':'complete CompCert assembly; signed source roots and address parameters, two actual stable pointers with independent/shared/overlapping storage, checked mapped/scheduled/tiled candidates, complete source fallback and public exits'}
 (WORK/('smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
