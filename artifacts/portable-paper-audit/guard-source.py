import json,os,sys
_FORBIDDEN=os.path.realpath(os.environ['PORTABLE_FORBIDDEN_ROOT'])
_LOG=os.environ['PORTABLE_AUDIT_LOG']
_busy=False
def _record(row):
 global _busy
 if _busy:return
 _busy=True
 try:
  with open(_LOG,'a') as f:f.write(json.dumps(row)+'\n')
 finally:_busy=False
def _check(path):
 if isinstance(path,(str,bytes,os.PathLike)):
  path=os.path.realpath(os.fsdecode(path))
  if path==_FORBIDDEN or path.startswith(_FORBIDDEN+os.sep):
   _record({'event':'denied_workspace_access','path':path,'pid':os.getpid()})
   raise PermissionError('Portable audit forbids original workspace: '+path)
def _audit(event,args):
 if _busy:return
 if event in ('open','os.listdir','os.scandir') and args:_check(args[0])
 if event=='subprocess.Popen':
  executable,argv=args[:2]
  for item in argv if isinstance(argv,(list,tuple)) else [argv]:
   if isinstance(item,str) and _FORBIDDEN in item:
    _record({'event':'denied_workspace_command','argv':argv,'pid':os.getpid()})
    raise PermissionError('Portable audit forbids original workspace command')
  if os.path.basename(os.fsdecode(executable)) in ('lake','lean','leanc'):
   _record({'event':'denied_lean_process','argv':argv,'pid':os.getpid()})
   raise PermissionError('Portable audit forbids Lean/Lake')
  _record({'event':'subprocess','argv':argv,'pid':os.getpid()})
sys.addaudithook(_audit)
_record({'event':'python_guard_active','pid':os.getpid(),'cwd':os.getcwd(),'python':sys.version})
