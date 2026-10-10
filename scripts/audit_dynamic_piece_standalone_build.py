"""Calibrate inherited build metadata against the actual standalone Driver root."""
import json
from pathlib import Path
from audit_interface_clight import ROOT,sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

BUILD=ROOT/'build/double-tree-model/compiler-attempts/native-dynamic-piece-standalone-v2/report.json'
PROOF=ROOT/'build/dynamic-piece-factory/proof-v1/report.json'
WORK=ROOT/'build/dynamic-piece-factory/standalone-build-v1'


def main():
    bindings={}
    build,proof=[checked(path,bindings) for path in [BUILD,PROOF]]
    entry='DoublePieceTreeCompiler.compile_selected_piece_double_tree_program'
    if build['status']!='built' or build['whole_program_entrypoint']!=entry:
        raise ValueError('Require the actual standalone compiler')
    if entry+'_correct' not in proof['endpoints']:
        raise ValueError('Require the existing audited whole-program theorem')
    driver=permitted(BUILD.parent/'driver/Driver.ml').read_text()
    if driver.count(entry+' ')!=1 or 'PieceCombinedDoubleCompiler.compile_selected_piece_combined_double_program ' in driver:
        raise ValueError('Driver must select exactly the standalone checked piece root')
    extraction=permitted(BUILD.parent/'ExtractSelectedDouble.v').read_text()
    if 'Separate Extraction '+entry not in extraction:
        raise ValueError('Require standard Rocq extraction of that root')
    report={key:value for key,value in build.items() if key!='bindings'}
    corrections={
        'established_typed_double_pipeline_runs_after_tree_pass':False,
        'literal_normalization_and_fixed_bound_pass_precede_combined_passes':False,
        'literal_factory_passes_exact_parameter_intervals':False,
        'per_statement_constant_point_shifts_and_actual_new_factory_extracted':False,
    }
    report.update(corrections)
    report.update(standalone_piece_pass_before_standard_CompCert_backend=True,
        actual_call_graph_calibrated=True,
        parent_metadata_describes_combined_capabilities_and_requires_these_corrections=corrections,
        no_new_proof_endpoints_or_axioms=True,
        parent_report=str(BUILD.relative_to(ROOT)),proof_report=str(PROOF.relative_to(ROOT)))
    WORK.mkdir(parents=True,exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))]=sha(permitted(Path(__file__)))
    report['bindings']=bindings
    (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'built','root':entry,'bindings':len(bindings)}),flush=True)


if __name__=='__main__':
    main()
