"""Focused real Hets/CASL replay with explicit premise lists and saved logs."""
from pathlib import Path
import hashlib,json,re,subprocess,os
import shutil

D=Path(__file__).resolve().parent
default_runtime=Path('/workspace/scratch/1b57605772cd/s4_moonshine/runtime/bin')
R=Path(os.environ['TORSER_HETS_BIN']) if os.environ.get('TORSER_HETS_BIN') else (default_runtime if default_runtime.exists() else None)
HETS=str(R/'hets') if R else (shutil.which('hets') or 'hets')
SPEC=D/'Native_Clock_Torser.het'
C=D/'checks';C.mkdir(exist_ok=True)
groups=[]
def group(name):
    goals=[];groups.append((name,goals));return goals
def g(goals,name,premises,prover='EProver'):goals.append((name,premises.split(),prover))

matrix=group('NativeClockConcreteMatrix')
g(matrix,'nt_native_decoder_exact','nc_rho_def nc_delta_def nc_native_constructor_cases')
g(matrix,'nt_native_representation_faithful','nt_native_decoder_exact')
ring='nc_add_assoc nc_add_comm nc_add_zero nc_add_inverse nc_mul_left_one nc_mul_right_one nc_mul_left_zero nc_mul_right_zero nc_negative_sum nc_negative_twice nc_negative_zero nc_negative_left nc_negative_right nc_left_distributes nc_right_distributes'
g(matrix,'nt_operator_rho_preserves_ordered_product',ring+' nc_native_product_def nc_matrix_product_def nc_rho_def nc_native_constructor_cases','SPASS')
g(matrix,'nt_context_work_cocycle_is_native_product',ring+' nc_weighted_product_def nc_weighted_matrix_def nc_rho_def nc_matrix_product_def nc_weighted_constructor_cases','SPASS')
g(matrix,'nt_source_natural_clock_adds_in_native_block',ring+' nc_clock_def nc_rho_def nc_matrix_product_def nc_nat_sum_interpretation','SPASS')
g(matrix,'nt_native_clock_reflects_original_integer','nc_clock_def nt_native_representation_faithful ga_injective_ncNative nc_nat_embedding_injective')

dagger=group('NativeClockAdjointInterpretation')
g(dagger,'nt_native_dagger_reverses_composition','nc_dagger_def nc_matrix_associative nc_matrix_star_reverses nc_gram_inverse_right nc_matrix_right_identity nc_matrix_left_identity','SPASS')
g(dagger,'nt_native_dagger_involutive','nc_dagger_def nc_matrix_associative nc_matrix_star_reverses nc_matrix_star_involutive nc_gram_self_adjoint nc_gram_inverse_self_adjoint nc_gram_inverse_left nc_gram_inverse_right nc_matrix_left_identity nc_matrix_right_identity','SPASS')

frame=group('NativeClockFrameInterpretation')
g(frame,'nt_framed_clock_composition_cancels_middle_chart','nt_frame_change_def nc_matrix_associative nt_frame_matrix_left_inverse nc_matrix_left_identity nc_matrix_right_identity','SPASS')
g(frame,'nt_framed_native_operator_returns_exactly','nt_frame_change_def nc_matrix_associative nt_frame_matrix_left_inverse nt_frame_matrix_right_inverse nc_matrix_left_identity nc_matrix_right_identity nt_actual_six_frame_cases '+' '.join('nt_frame_inverse_'+x for x in ['e','r','rr','s','sr','srr']),'SPASS')

state=group('NativeClockTorserState')
g(state,'nt_full_original_state_roundtrip','nt_encode_state_definition nt_decode_state_definition')
g(state,'nt_full_native_state_roundtrip','nt_encode_state_definition nt_decode_state_definition nt_decode_frame_definition nt_native_state_constructor_cases')
g(state,'nt_same_actual_source_step','nt_encode_state_definition nt_decode_state_definition nt_native_step_definition')
g(state,'nt_history_returns_the_whole_original_state','nt_tick_definition nt_undo_definition nt_local_record_inverse nt_source_record_constructor_cases')
statecases='nt_native_state_constructor_cases nt_source_record_constructor_cases'
g(state,'nt_tick_retains_original_input','nt_native_step_definition nt_tick_definition nt_source_definition ga_selector_ntsInput '+statecases,'SPASS')
g(state,'nt_tick_is_one_actual_original_tick','nt_native_step_definition nt_tick_definition nt_clock_record_definition ga_selector_ntsClock '+statecases,'SPASS')
g(state,'nt_initial_retains_original_input','nt_initial_definition nt_source_definition ga_selector_ntsInput')
g(state,'nt_initial_clock_zero','nt_initial_definition nt_clock_record_definition ga_selector_ntsClock')
g(state,'nt_operational_fredkin_original_wires','rg_fredkin_inverse')
g(state,'nt_operational_toffoli_original_wires','rg_toffoli_inverse')

run=group('NativeClockTorserRun')
g(run,'nt_clock_identity_case','nt_complete_run_invariant_definition nt_identity_begin nt_identity_end nt_identity_work cd_add_z')
g(run,'nt_clock_actual_tick_case','nt_complete_run_invariant_definition nt_primitive_begin nt_primitive_end nt_primitive_work nt_tick_retains_original_input nt_tick_is_one_actual_original_tick cd_add_s cd_add_z')
g(run,'nt_clock_composition_case','nt_complete_run_invariant_definition nt_compose_begin nt_compose_end nt_costed_composition_work nt_costed_composition_rule nt_nat_associativity_interpretation','SPASS')
g(run,'nt_clock_presentation_case','nt_complete_run_invariant_definition nt_presentation_begin nt_presentation_end nt_presentation_no_executed_operation nt_pure_presentation_rule')
g(run,'nt_clock_terminal_case','nt_complete_run_invariant_definition nt_terminal_begin nt_terminal_end nt_terminal_proof_no_hidden_execution nt_terminal_original_receipt_rule')
g(run,'nt_complete_original_clock_invariant','nt_free_execution_proof_induction nt_clock_identity_case nt_clock_actual_tick_case nt_clock_composition_case nt_clock_presentation_case nt_clock_terminal_case')
g(run,'nt_complete_run_packet_return','nt_run_codec_retains_complete_proof nt_run_decoder_retains_complete_proof')
g(run,'nt_run_transport_retains_actual_bit_work','nt_run_codec_retains_complete_proof')

end=group('NativeClockH24Rules')
g(end,'nt_upper_reserve_has_exact_native_clock_equation','nt_upper_reserve_rule_definition nt_source_natural_clock_adds_in_native_block')
g(end,'nt_tight_tick_consumes_exactly_one_original_unit','nt_tight_reserve_definition nt_upper_reserve_rule_definition cd_add_z')
g(end,'nt_terminal_rule_constructs_original_verifier_minimum','nt_terminal_original_receipt_rule rr_root_receipt_gives_minimum')
g(end,'nt_native_minimum_returns_all_original_competitors','nt_terminal_native_minimum_definition nt_terminal_rule_constructs_original_verifier_minimum nt_terminal_original_receipt_rule nt_complete_original_clock_invariant nt_complete_run_invariant_definition nt_initial_retains_original_input')
g(end,'nt_native_terminal_tag_returns_original_sat','nt_native_minimum_returns_all_original_competitors vm_shortest_tag_decides_original')
g(end,'nt_native_minimum_reference_returns_original_refutation','nt_native_minimum_returns_all_original_competitors vm_shortest_fallback_iff_refutation')

uniform=group('NativeClockUniformTarget')
g(uniform,'nt_native_deadline_is_same_original_deadline','nt_native_by_frozen_clock_definition nt_monitor_same_original_hit_and_tick cd_affirmative_by_exact_clock')
g(uniform,'nt_full_class_same_machine_same_clock','nt_uniform_native_target_full_quantifiers nt_monitor_same_original_hit_and_tick nt_native_deadline_is_same_original_deadline cd_pass_def cd_sound_def cd_timely_def','SPASS')
g(uniform,'nt_uniform_native_clock_decides_original_negative','nt_full_class_same_machine_same_clock nt_native_deadline_is_same_original_deadline cd_pass_decides_at_one_clock')
g(uniform,'nt_whole_quantified_bridge_returns_to_original_source','nt_whole_native_clock_definition nt_monitor_constructor_cases nt_full_class_same_machine_same_clock')
g(uniform,'nt_native_whole_clock_iff_original_stopped_decider','nt_whole_quantified_bridge_returns_to_original_source cd_uniform_exists_equivalence')

def main():
    env=os.environ.copy()
    if R:env['PATH']=str(R)+os.pathsep+env.get('PATH','')
    commands=[]
    for node,goals in groups:
        commands += ['dg basic '+node,'set include-theorems true','set time-limit 4']
        for name,premises,prover in goals:
            commands += ['prover '+prover,'set goals '+name,'set axioms '+' '.join(premises),'prove']
    commands += ['quit','']
    (C/'replay.commands').write_text('\n'.join(commands))
    p=subprocess.run([HETS,'-L',str(D/'deps'),'-A','-I',str(SPEC)],cwd=D,
                     input='\n'.join(commands),text=True,capture_output=True,env=env,timeout=220)
    log=p.stdout+'\n'+p.stderr;(C/'hets-casl-replay.log').write_text(log)
    proved=re.findall(r'^Goal (\w+) is proved\.$',log,re.M)
    schedule=[dict(spec=n,goal=g,premises=p,prover=v,status='proved' if g in proved else 'not_discharged_in_this_run')
              for n,gs in groups for g,p,v in gs]
    allgoals=re.findall(r'%\((\w+)\)%\s*%implied',SPEC.read_text())
    selected={g['goal'] for g in schedule}
    out=dict(hets_command=HETS,source=str(SPEC),sha256=hashlib.sha256(SPEC.read_bytes()).hexdigest(),
             process_exit=p.returncode,static_analysis='succeeded' if 'Analyzing spec NativeClockUniformTarget' in log and p.returncode==0 else 'inspect log',
             selected_goal_count=len(schedule),proved_count=len(proved),goals=schedule,
             source_obligations_outside_selected_schedule=[g for g in allgoals if g not in selected],
             interpretation_premises='Concrete ring, natural embedding, matrix and Gram laws are specified and independently checked; the local record inverse is a fixed-machine implementation interface. No source correctness or all-CNF polynomial-bound target is assumed.',
             imported_source_theorems='Original named Native_Shortest_Proof conclusions are reused; this run does not reprove the complete historical parent library.',
             other_proof_method='checks/native-algebra-certificate.json independently closes the universal ordered-algebra identities.')
    (C/'casl-replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'selected':len(schedule),'proved':len(proved),'not_discharged':[q['goal'] for q in schedule if q['status']!='proved'],'exit':p.returncode}))
if __name__=='__main__':main()
