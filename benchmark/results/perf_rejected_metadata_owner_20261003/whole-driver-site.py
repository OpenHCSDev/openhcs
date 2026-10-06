import functools, hashlib, importlib.abc, importlib.machinery, inspect, json, os, sys, threading, time
from pathlib import Path
SOURCE=Path(os.environ['OPENHCS_DIAGNOSTIC_SOURCE']).resolve()
OUT=Path(os.environ['OPENHCS_DIAGNOSTIC_OUTPUT'])
freeze=json.loads(Path(os.environ['OPENHCS_DIAGNOSTIC_FREEZE']).read_text())
assert not os.environ.get('OPENHCS_WORKER_PROFILE_DIR'), 'Worker profiler must be disabled.'
assert os.environ.get('OPENHCS_PROFILE_FUNCTION_RUNTIME','').lower() not in {'1','true','yes'}, 'Runtime profiler must be disabled.'
assert not os.environ.get('OPENHCS_PROFILE_FUNCTION_RUNTIME_PATH'), 'No runtime profiler sink.'
active=threading.local()
installed=[]
TARGETS = {'openhcs.runtime.zmq_execution_server': {'ZMQExecutionServer': ('_execute_with_orchestrator', '_initialize_orchestrator', '_export_runtime_observation')}, 'openhcs.core.orchestrator.worker_execution': {'': ('execute_worker_lane',)}, 'openhcs.core.steps.function_runtime': {'FunctionCoreExecutor': ('execute',), 'PatternGroupRuntime': ('_load_input_stack', '_validate_and_unstack', '_save_outputs')}, 'openhcs.processing.backends.lib_registry.unified_registry': {'RuntimeCallableInvocation': ('call',)}, 'openhcs.interop.cellprofiler.runtime.module_execution': {'CellProfilerModuleExecutor': ('__call__', '_image_request')}, 'openhcs.interop.cellprofiler.runtime.function_contract_execution': {'CellProfilerFunctionContractExecutor': ('execute',)}, 'openhcs.interop.cellprofiler.runtime.output_recording': {'CellProfilerOutputRecorder': ('record_module_outputs',)}, 'openhcs.interop.cellprofiler.runtime.measurement_execution_support': {'ObjectMeasurementOutputRecorder': ('record',)}, 'openhcs.core.steps.function_outputs': {'': ('finalize_function_step_outputs',), 'OpenHCSMetadataWriter': ('finalize_completed_plate',), 'RuntimeArtifactMetadataTarget': ('reconciliation_targets',)}, 'openhcs.core.virtual_workspace_metadata': {'AtomicMetadataWriter': ('publish_source_projection_metadata',)}, 'openhcs.core.runtime_stack_cache': {'RuntimeImageStackCache': ('get', 'store')}, 'openhcs.core.aligned_image_payload': {'': ('stack_image_payload_context', 'unstack_image_payload_context')}, 'openhcs.core.orchestrator.analysis_consolidation': {'': ('consolidate_analysis_outputs',)}, 'openhcs.core.measurement_feature_queries': {'MeasurementFeatureValueIndex': ('from_columnar_table_by_object',)}}
PHASES = {'ZMQExecutionServer._execute_with_orchestrator': '_execute_with_orchestrator', 'ZMQExecutionServer._initialize_orchestrator': '_initialize_orchestrator', 'ZMQExecutionServer._export_runtime_observation': '_export_runtime_observation', 'execute_worker_lane': 'execute_worker_lane', 'FunctionCoreExecutor.execute': 'execute', 'PatternGroupRuntime._load_input_stack': '_load_input_stack', 'PatternGroupRuntime._validate_and_unstack': '_validate_and_unstack', 'PatternGroupRuntime._save_outputs': '_save_outputs', 'RuntimeCallableInvocation.call': 'declared_callable_boundary', 'CellProfilerModuleExecutor.__call__': '__call__', 'CellProfilerModuleExecutor._image_request': '_image_request', 'CellProfilerFunctionContractExecutor.execute': 'execute', 'CellProfilerOutputRecorder.record_module_outputs': 'record_module_outputs', 'ObjectMeasurementOutputRecorder.record': 'record', 'finalize_function_step_outputs': 'finalize_function_step_outputs', 'OpenHCSMetadataWriter.finalize_completed_plate': 'finalize_completed_plate', 'RuntimeArtifactMetadataTarget.reconciliation_targets': 'reconciliation_targets', 'AtomicMetadataWriter.publish_source_projection_metadata': 'publish_source_projection_metadata', 'RuntimeImageStackCache.get': 'get', 'RuntimeImageStackCache.store': 'store', 'stack_image_payload_context': 'stack_image_payload_context', 'unstack_image_payload_context': 'unstack_image_payload_context', 'consolidate_analysis_outputs': 'consolidate_analysis_outputs', 'MeasurementFeatureValueIndex.from_columnar_table_by_object': 'measurement_feature_index'}
ROOTS = {'ZMQExecutionServer._execute_with_orchestrator', 'execute_worker_lane'}
def detail(label, args, kwargs):
    if label == "ZMQExecutionServer._execute_with_orchestrator":
        request = kwargs.get("request_context") if "request_context" in kwargs else args[1]
        selected = request.request_payload.selected_pipeline_path
        return json.dumps({"kind": "compile_only" if request.compile_only else "execution", "plate": str(request.plate_id), "case": None if selected is None else Path(selected).stem, "execution_id": request.execution_id, "compile_artifact_id": request.compile_artifact_id}, sort_keys=True)
    if label == "execute_worker_lane":
        lane = kwargs.get("lane_context") if "lane_context" in kwargs else args[2]
        return json.dumps({"kind": "worker_lane", "plate": str(lane.plate_id), "worker_slot": lane.worker_slot, "execution_id": lane.execution_id}, sort_keys=True)
    if label.startswith('FunctionStepExecutor.'):
        plan = args[0].plan
        return f'step={plan.step_index}:{plan.step_name}'
    if label.startswith('FunctionCoreExecutor.'):
        return 'function=' + args[0].function_name
    if label == 'CellProfilerFunctionContractExecutor.execute':
        contract = kwargs.get('callable_contract') if 'callable_contract' in kwargs else args[1]
        return 'function=' + contract.module_name + '.' + contract.function_name
    if label == 'RuntimeCallableInvocation.call':
        invocation = args[0]
        func = invocation.func
        return 'function=' + func.__module__ + '.' + func.__qualname__ + ';view=' + str(invocation.callable_view.value)
    return ''

def safe_detail(label,args,kwargs):
 try:return detail(label,args,kwargs)
 except Exception as error:
  active.diagnostic_errors.append({'owner':label,'type':type(error).__name__,'message':str(error)})
  return 'DIAGNOSTIC_DETAIL_UNAVAILABLE'

def reset_fork():
 global active
 active=threading.local()
os.register_at_fork(after_in_child=reset_fork)
def instrument(original, label):
 @functools.wraps(original)
 def wrapped(*args, **kwargs):
  root=not getattr(active, 'enabled', False)
  if root and label not in ROOTS:
   return original(*args, **kwargs)
  if root:
   active.enabled=True; active.stats={}; active.stack=[]; active.diagnostic_errors=[]; active.root_dimensions=safe_detail(label,args,kwargs)
  dimensions=safe_detail(label,args,kwargs)
  name=label+(' | '+dimensions if dimensions else '')
  frame={'start':time.perf_counter(), 'children':0.}
  active.stack.append(frame)
  try:
   return original(*args,**kwargs)
  finally:
   elapsed=time.perf_counter()-frame['start']
   assert active.stack.pop() is frame
   row=active.stats.setdefault(name, {'owner':label,'dimensions':dimensions,'phase':PHASES[label],'calls':0,'inclusive':0.,'exclusive':0.})
   row['calls']+=1; row['inclusive']+=elapsed; row['exclusive']+=elapsed-frame['children']
   if active.stack:
    active.stack[-1]['children']+=elapsed
   if root:
    active.enabled=False
    sequence=getattr(active,'sequence',0)+1;active.sequence=sequence
    path=OUT/f'region-{os.getpid()}-{threading.get_ident()}-{sequence:04}.json'
    assert not path.exists()
    value={'pid':os.getpid(),'thread':threading.get_ident(),'region':label,'root_dimensions':active.root_dimensions,'seconds':elapsed,'revision':freeze['revision'],'source':str(SOURCE),'stats':active.stats,'hooks_installed':installed,'profiling_enabled':False,'runtime_profiling_enabled':False,'diagnostic_errors':active.diagnostic_errors,'captures':False,'scope':'coarse same-run nested exclusive timing partition on the exact source revision recorded in this region. Diagnostic wrappers, no scientific or memory-observer substitutions. Not accepted performance comparison. Declared callable boundary includes filtering/decorated processing/metadata; not pure numerical kernels. Both existing profilers are disabled. These wrappers still add diagnostic overhead; no scaling to uninstrumented clocks or causal performance claims. Query boundary is nested under its actual parent and excluded from parent-exclusive elapsed.'}
    assert abs(sum(r['exclusive'] for r in active.stats.values())-elapsed)<1e-6
    path.write_text(json.dumps(value,indent=2)+'\n')
 return wrapped
class Loader(importlib.abc.InspectLoader):
 def __init__(self, loader): self.loader=loader
 def create_module(self,spec): return self.loader.create_module(spec)
 def get_code(self,fullname): return self.loader.get_code(fullname)
 def get_source(self,fullname): return self.loader.get_source(fullname)
 def is_package(self,fullname): return self.loader.is_package(fullname)
 def get_filename(self,fullname): return self.loader.get_filename(fullname)
 def exec_module(self,module):
  self.loader.exec_module(module)
  path=Path(module.__file__).resolve();relative=str(path.relative_to(SOURCE))
  assert hashlib.sha256(path.read_bytes()).hexdigest()==freeze['files'][relative]
  for owner_path,names in TARGETS[module.__name__].items():
   owner=module
   for part in owner_path.split('.') if owner_path else (): owner=getattr(owner,part)
   for name in names:
    descriptor=inspect.getattr_static(owner,name)
    declared_original=descriptor.__func__ if isinstance(descriptor,(classmethod,staticmethod)) else descriptor
    original_signature=inspect.signature(declared_original)
    original_code=declared_original.__code__
    source_declared=inspect.unwrap(declared_original)
    assert Path(source_declared.__code__.co_filename).resolve()==path,(module.__name__,owner_path,name,source_declared.__code__.co_filename)
    label=(owner_path+'.' if owner_path else '')+name
    if isinstance(descriptor,classmethod): replacement=classmethod(instrument(descriptor.__func__,label));kind='classmethod'
    elif isinstance(descriptor,staticmethod):replacement=staticmethod(instrument(descriptor.__func__,label));kind='staticmethod'
    else:
     assert callable(descriptor),(owner_path,name)
     replacement=instrument(descriptor,label);kind='function'
    setattr(owner,name,replacement)
    assert type(inspect.getattr_static(owner,name)) is type(replacement)
    wrapped_descriptor=inspect.getattr_static(owner,name)
    wrapped_function=wrapped_descriptor.__func__ if isinstance(wrapped_descriptor,(classmethod,staticmethod)) else wrapped_descriptor
    assert wrapped_function.__wrapped__ is declared_original
    assert inspect.signature(wrapped_function)==original_signature
    assert wrapped_function.__wrapped__.__code__ is original_code
    installed.append({'module':module.__name__,'owner':owner_path,'method':name,'descriptor_kind':kind})
class Finder(importlib.abc.MetaPathFinder):
 def find_spec(self,fullname,path=None,target=None):
  if fullname not in TARGETS:return None
  spec=importlib.machinery.PathFinder.find_spec(fullname,path,target)
  assert spec is not None and isinstance(spec.loader,importlib.machinery.SourceFileLoader)
  spec.loader=Loader(spec.loader)
  return spec
sys.meta_path.insert(0,Finder())
