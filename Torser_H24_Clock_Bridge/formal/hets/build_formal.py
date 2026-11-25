from pathlib import Path
import sys, json, hashlib, shutil

D=Path(__file__).resolve().parent
B=D.parents[1]
D.mkdir(parents=True,exist_ok=True)
(D/'deps').mkdir(exist_ok=True)
source=B/'pnp_agent_native/originals/Native_Shortest_Proof.het'
if not source.exists():source=D/'deps/Native_Shortest_Proof.het'
if source.resolve()!=(D/'deps/Native_Shortest_Proof.het').resolve():
    shutil.copyfile(source,D/'deps/Native_Shortest_Proof.het')
old=B/'pnp_work/extracted/PNP_Multiple_Constructions/PNP_Multiple_Constructions'
sys.path.insert(0,str(old/'algebra' if old.exists() else D/'deps/native_algebra'))
import torsor_matrix as frames

parts=[]
def put(s): parts.append(s.strip()+'\n')
put(r'''
library Native_Clock_Torser
from Native_Shortest_Proof get FixedMonitorClock, NativeRootMatrix, CechReversibleGates
logic CASL

%% New native clock/shortest-verifier bridge. Source definitions are imported.
%% %implied marks obligations, not automatically a successful prover result.
%% Original source ticks, compiled implementation ticks and output length
%% are separate fields. NTSourceClock is interpreted as history length.

spec NativeClockCoefficientData = FixedMonitorClock then
  sort NCoeff
  ops nc0,nc1,ncThird : NCoeff;
      ncAdd,ncMul : NCoeff * NCoeff -> NCoeff;
      ncNeg,ncStar : NCoeff -> NCoeff;
      ncOfNat : VNat -> NCoeff
  forall a,b,c : NCoeff
  . ncAdd(ncAdd(a,b),c)=ncAdd(a,ncAdd(b,c)) %(nc_add_assoc)%
  . ncAdd(a,b)=ncAdd(b,a) %(nc_add_comm)%
  . ncAdd(nc0,a)=a %(nc_add_zero)%
  . ncAdd(a,ncNeg(a))=nc0 %(nc_add_inverse)%
  . ncMul(ncMul(a,b),c)=ncMul(a,ncMul(b,c)) %(nc_mul_assoc)%
  . ncMul(nc1,a)=a %(nc_mul_left_one)%
  . ncMul(a,nc1)=a %(nc_mul_right_one)%
  . ncMul(nc0,a)=nc0 %(nc_mul_left_zero)%
  . ncMul(a,nc0)=nc0 %(nc_mul_right_zero)%
  . ncMul(a,ncAdd(b,c))=ncAdd(ncMul(a,b),ncMul(a,c)) %(nc_left_distributes)%
  . ncMul(ncAdd(a,b),c)=ncAdd(ncMul(a,c),ncMul(b,c)) %(nc_right_distributes)%
  . ncNeg(ncAdd(a,b))=ncAdd(ncNeg(a),ncNeg(b)) %(nc_negative_sum)%
  . ncNeg(ncNeg(a))=a %(nc_negative_twice)%
  . ncNeg(nc0)=nc0 %(nc_negative_zero)%
  . ncMul(ncNeg(a),b)=ncNeg(ncMul(a,b)) %(nc_negative_left)%
  . ncMul(a,ncNeg(b))=ncNeg(ncMul(a,b)) %(nc_negative_right)%
  . ncStar(ncStar(a))=a %(nc_star_involution)%
  . ncStar(ncAdd(a,b))=ncAdd(ncStar(a),ncStar(b)) %(nc_star_sum)%
  . ncStar(ncMul(a,b))=ncMul(ncStar(b),ncStar(a)) %(nc_star_product)%
  . ncStar(ncNeg(a))=ncNeg(ncStar(a)) %(nc_star_negative)%
  . ncStar(nc0)=nc0 %(nc_star_zero)%
  . ncStar(nc1)=nc1 %(nc_star_one)%
  . ncStar(ncThird)=ncThird %(nc_star_third)%
  . ncMul(ncThird,ncAdd(nc1,ncAdd(nc1,nc1)))=nc1 %(nc_third_inverse)%
  . ncMul(ncThird,a)=ncMul(a,ncThird) %(nc_third_central)%
  . not nc0=nc1 %(nc_nontrivial)%
  %% Standard characteristic-zero natural-number interpretation, not a time axiom.
  forall n,m : VNat; a : NCoeff
  . ncOfNat(vZ)=nc0 %(nc_nat_zero)%
  . ncOfNat(vS(n))=ncAdd(nc1,ncOfNat(n)) %(nc_nat_successor)%
  . ncOfNat(cdAdd(n,m))=ncAdd(ncOfNat(n),ncOfNat(m)) %(nc_nat_sum_interpretation)%
  . ncOfNat(n)=ncOfNat(m) => n=m %(nc_nat_embedding_injective)%
  . ncMul(ncOfNat(n),a)=ncMul(a,ncOfNat(n)) %(nc_nat_central)%
  . ncStar(ncOfNat(n))=ncOfNat(n) %(nc_nat_star)%
end

spec NativeClockConcreteMatrix = NativeClockCoefficientData then
  free type NCNative ::= ncNative(NCoeff;NCoeff;NCoeff;NCoeff;NCoeff;NCoeff)
  free type NCMatrix ::= ncMatrix(NCoeff;NCoeff;NCoeff;NCoeff;
                                  NCoeff;NCoeff;NCoeff;NCoeff;
                                  NCoeff;NCoeff;NCoeff;NCoeff;
                                  NCoeff;NCoeff;NCoeff;NCoeff)
  free type NCWeighted ::= ncWeighted(NCoeff;NCoeff)
  ops ncNativeProduct : NCNative * NCNative -> NCNative;
      ncRho : NCNative -> NCMatrix;
      ncDelta : NCMatrix -> NCNative;
      ncMMul : NCMatrix * NCMatrix -> NCMatrix;
      ncMStar : NCMatrix -> NCMatrix;
      ncI,ncJ,ncJInv : NCMatrix;
      ncDagger : NCMatrix -> NCMatrix;
      ncClock : VNat -> NCMatrix;
      ncWeightedProduct : NCWeighted * NCWeighted -> NCWeighted;
      ncWeightedMatrix : NCWeighted -> NCMatrix
  %% Explicit elimination of these declared free constructors for FOL provers.
  forall a : NCNative
  . exists t,b,p,q,r,s : NCoeff . a=ncNative(t,b,p,q,r,s) %(nc_native_constructor_cases)%
  forall w : NCWeighted
  . exists p,c : NCoeff . w=ncWeighted(p,c) %(nc_weighted_constructor_cases)%
  forall t,b,p,q,r,s,u,c,h,i,j,k : NCoeff
  . ncNativeProduct(ncNative(t,b,p,q,r,s),ncNative(u,c,h,i,j,k))=
      ncNative(ncMul(t,u),
        ncAdd(ncAdd(ncMul(t,c),ncMul(b,u)),ncNeg(ncAdd(ncMul(b,c),ncMul(b,c)))),
        ncAdd(ncMul(p,h),ncMul(q,j)),ncAdd(ncMul(p,i),ncMul(q,k)),
        ncAdd(ncMul(r,h),ncMul(s,j)),ncAdd(ncMul(r,i),ncMul(s,k))) %(nc_native_product_def)%
  . ncRho(ncNative(t,b,p,q,r,s))=
      ncMatrix(ncAdd(t,ncNeg(ncAdd(b,b))),nc0,nc0,nc0,
               nc0,p,q,nc0,nc0,r,s,nc0,b,nc0,nc0,t) %(nc_rho_def)%
  forall n : VNat
  . ncClock(n)=ncRho(ncNative(nc1,nc0,nc1,ncOfNat(n),nc0,nc1)) %(nc_clock_def)%
  forall p,w,q,z : NCoeff
  . ncWeightedProduct(ncWeighted(q,z),ncWeighted(p,w))=
      ncWeighted(ncMul(q,p),ncAdd(ncMul(q,w),ncMul(z,p))) %(nc_weighted_product_def)%
  . ncWeightedMatrix(ncWeighted(p,w))=ncRho(ncNative(p,nc0,p,w,nc0,p)) %(nc_weighted_matrix_def)%
''')

av=[f'a{i}{j}' for i in range(1,5) for j in range(1,5)]
bv=[f'b{i}{j}' for i in range(1,5) for j in range(1,5)]
def mat(v):return 'ncMatrix('+','.join(v)+')'
def add(v):return v[0] if len(v)==1 else 'ncAdd('+v[0]+','+add(v[1:])+')'
put('  forall '+','.join(av+bv)+' : NCoeff\n  . ncMMul('+mat(av)+','+mat(bv)+')=\n      '+mat([add([f'ncMul(a{i}{k},b{k}{j})' for k in range(1,5)]) for i in range(1,5) for j in range(1,5)])+' %(nc_matrix_product_def)%')
put('  forall '+','.join(av)+' : NCoeff\n  . ncDelta('+mat(av)+')=ncNative(a44,a41,a22,a23,a32,a33) %(nc_delta_def)%\n  . ncMStar('+mat(av)+')='+mat([f'ncStar(a{j}{i})' for i in range(1,5) for j in range(1,5)])+' %(nc_matrix_star_def)%')
zero='nc0';one='nc1';two='ncAdd(nc1,nc1)';minus='ncNeg(nc1)';third='ncThird';twothird='ncAdd(ncThird,ncThird)'
put('  . ncI='+mat([one if i==j else zero for i in range(4) for j in range(4)])+' %(nc_identity_def)%')
put('  . ncJ='+mat([one,zero,zero,one, zero,two,minus,zero, zero,minus,two,zero, one,zero,zero,two])+' %(nc_gram_def)%')
put('  . ncJInv='+mat([two,zero,zero,minus, zero,twothird,third,zero, zero,third,twothird,zero, minus,zero,zero,one])+' %(nc_gram_inverse_def)%')
put(r'''
  forall m : NCMatrix
  . ncDagger(m)=ncMMul(ncJInv,ncMMul(ncMStar(m),ncJ)) %(nc_dagger_def)%
  forall a,b : NCNative; n,m : VNat; u,v : NCWeighted
  . ncDelta(ncRho(a))=a %(nt_native_decoder_exact)% %implied
  . ncRho(a)=ncRho(b) => a=b %(nt_native_representation_faithful)% %implied
  . ncRho(ncNativeProduct(a,b))=ncMMul(ncRho(a),ncRho(b)) %(nt_operator_rho_preserves_ordered_product)% %implied
  . ncWeightedMatrix(ncWeightedProduct(u,v))=ncMMul(ncWeightedMatrix(u),ncWeightedMatrix(v))
      %(nt_context_work_cocycle_is_native_product)% %implied
  . ncMMul(ncClock(n),ncClock(m))=ncClock(cdAdd(n,m)) %(nt_source_natural_clock_adds_in_native_block)% %implied
  . ncClock(n)=ncClock(m) => n=m %(nt_native_clock_reflects_original_integer)% %implied
end

%% Matrix/adjoint laws are the concrete interpretation of the preceding
%% finite matrix definitions over the coefficient ring. Their full ordered
%% polynomial verification is retained separately; no cost claim is a premise.
spec NativeClockAdjointInterpretation = NativeClockConcreteMatrix then
  forall a,b,c : NCMatrix
  . ncMMul(ncMMul(a,b),c)=ncMMul(a,ncMMul(b,c)) %(nc_matrix_associative)%
  . ncMMul(ncI,a)=a %(nc_matrix_left_identity)%
  . ncMMul(a,ncI)=a %(nc_matrix_right_identity)%
  . ncMStar(ncMMul(a,b))=ncMMul(ncMStar(b),ncMStar(a)) %(nc_matrix_star_reverses)%
  . ncMStar(ncMStar(a))=a %(nc_matrix_star_involutive)%
  . ncMStar(ncJ)=ncJ %(nc_gram_self_adjoint)%
  . ncMStar(ncJInv)=ncJInv %(nc_gram_inverse_self_adjoint)%
  . ncMMul(ncJInv,ncJ)=ncI %(nc_gram_inverse_left)%
  . ncMMul(ncJ,ncJInv)=ncI %(nc_gram_inverse_right)%
  forall a,b : NCMatrix
  . ncDagger(ncMMul(a,b))=ncMMul(ncDagger(b),ncDagger(a)) %(nt_native_dagger_reverses_composition)% %implied
  . ncDagger(ncDagger(a))=a %(nt_native_dagger_involutive)% %implied
end

spec NativeClockSixFrames = NativeClockAdjointInterpretation then
  free type NTFrame ::= ntE | ntR | ntRR | ntS | ntSR | ntSRR
  ops ntFrameMul : NTFrame * NTFrame -> NTFrame;
      ntFrameInv : NTFrame -> NTFrame;
      ntFrameMatrix : NTFrame -> NCMatrix;
      ntFramed : NTFrame * NCMatrix * NTFrame -> NCMatrix
  forall g : NTFrame
  . g=ntE \/ g=ntR \/ g=ntRR \/ g=ntS \/ g=ntSR \/ g=ntSRR %(nt_actual_six_frame_cases)%
''')
names=dict(zip(frames.NAMES,['ntE','ntR','ntRR','ntS','ntSR','ntSRR']))
def nc_integer(i):
    if i==0:return 'nc0'
    if i==1:return 'nc1'
    if i<0:return 'ncNeg('+nc_integer(-i)+')'
    return 'ncAdd(nc1,'+nc_integer(i-1)+')'
for g in frames.NAMES:
    for h in frames.NAMES:
        put(f'  . ntFrameMul({names[g]},{names[h]})={names[frames.multiply(g,h)]} %(nt_frame_{g}_{h})%')
    put(f'  . ntFrameInv({names[g]})={names[frames.inverse(g)]} %(nt_frame_inverse_{g})%')
    put(f'  . ntFrameMatrix({names[g]})=ncRho(ncNative('+','.join(nc_integer(i) for i in frames.ELEMENTS[g])+f')) %(nt_frame_matrix_{g})%')
put(r'''
  forall g,h,k : NTFrame; m : NCMatrix
  . ntFramed(h,m,g)=ncMMul(ntFrameMatrix(h),ncMMul(m,ntFrameMatrix(ntFrameInv(g)))) %(nt_frame_change_def)%
  . ntFrameMul(ntFrameInv(h),ntFrameMul(h,g))=g %(nt_six_frames_exact_inverse)% %implied
  . ntFrameMul(k,ntFrameMul(h,g))=ntFrameMul(ntFrameMul(k,h),g) %(nt_six_frames_composition)% %implied
end

%% The finite frame interpretation, proved by the literal six matrices.
spec NativeClockFrameInterpretation = NativeClockSixFrames then
  forall g,h : NTFrame
  . ntFrameMatrix(ntFrameMul(g,h))=ncMMul(ntFrameMatrix(g),ntFrameMatrix(h)) %(nt_frame_matrix_representation)%
  . ntFrameMatrix(ntE)=ncI %(nt_frame_matrix_identity)%
  . ncMMul(ntFrameMatrix(g),ntFrameMatrix(ntFrameInv(g)))=ncI %(nt_frame_matrix_right_inverse)%
  . ncMMul(ntFrameMatrix(ntFrameInv(g)),ntFrameMatrix(g))=ncI %(nt_frame_matrix_left_inverse)%
  . ncDagger(ntFrameMatrix(g))=ntFrameMatrix(ntFrameInv(g)) %(nt_frame_gram_unitary)%
  forall g,h,k : NTFrame; a,b : NCMatrix
  . ncMMul(ntFramed(k,b,h),ntFramed(h,a,g))=ntFramed(k,ncMMul(b,a),g)
      %(nt_framed_clock_composition_cancels_middle_chart)% %implied
  . ntFramed(ntFrameInv(h),ntFramed(h,a,g),ntFrameInv(g))=a
      %(nt_framed_native_operator_returns_exactly)% %implied
end

spec NativeClockTorserState = NativeClockSixFrames and NativeRootMatrix and CechReversibleGates then
  sorts NTMState, NTEvent
  free type NTHistory ::= ntHNil | ntHCons(NTEvent;NTHistory)
  free type NTSourceRecord ::= ntSourceRecord(ntsInput:VInput;ntsMachine:NTMState;ntsHistory:NTHistory;ntsClock:VNat)
  free type NTNativeState ::= ntPacked(NTSourceRecord;NTFrame)
  ops ntInitialMachine : VInput -> NTMState;
      ntAdvance : NTMState -> NTMState;
      ntLocalEvent : NTMState -> NTEvent;
      ntRestore : NTEvent * NTMState -> NTMState;
      ntMachineOutput : NTMState -> VWord;
      ntEventFrame : NTEvent -> NTFrame;
      ntTick,ntUndo : NTSourceRecord -> NTSourceRecord;
      ntEncodeState : NTSourceRecord * NTFrame -> NTNativeState;
      ntDecodeState : NTNativeState -> NTSourceRecord;
      ntFrame : NTNativeState -> NTFrame;
      ntStep : NTNativeState -> NTNativeState;
      ntSource : NTNativeState -> VInput;
      ntOutput : NTNativeState -> VWord;
      ntClock : NTNativeState -> VNat;
      ntStart : VInput -> NTNativeState
  preds ntLiveMachine,ntHaltMachine : NTMState;
        ntEnabled,ntHalted : NTNativeState
  forall x : NTSourceRecord
  . exists c : VInput; s : NTMState; h : NTHistory; k : VNat .
       x=ntSourceRecord(c,s,h,k) %(nt_source_record_constructor_cases)%
  forall z : NTNativeState
  . exists x : NTSourceRecord; g : NTFrame . z=ntPacked(x,g) %(nt_native_state_constructor_cases)%
  %% Actual fixed local transition interface: an event retains only a fixed
  %% finite overwritten symbol/control record; this law is proved by undoing it.
  forall s : NTMState
  . ntRestore(ntLocalEvent(s),ntAdvance(s))=s %(nt_local_record_inverse)%
  forall c : VInput; s : NTMState; h : NTHistory; e : NTEvent; k : VNat; g : NTFrame; x : NTSourceRecord
  . ntTick(ntSourceRecord(c,s,h,k))=ntSourceRecord(c,ntAdvance(s),ntHCons(ntLocalEvent(s),h),vS(k)) %(nt_tick_definition)%
  . ntUndo(ntSourceRecord(c,s,ntHCons(e,h),vS(k)))=ntSourceRecord(c,ntRestore(e,s),h,k) %(nt_undo_definition)%
  . ntEncodeState(x,g)=ntPacked(x,g) %(nt_encode_state_definition)%
  . ntDecodeState(ntPacked(x,g))=x %(nt_decode_state_definition)%
  . ntFrame(ntPacked(x,g))=g %(nt_decode_frame_definition)%
  . ntStep(ntPacked(x,g))=ntPacked(ntTick(x),ntFrameMul(ntEventFrame(ntLocalEvent(ntsMachine(x))),g)) %(nt_native_step_definition)%
  . ntSource(ntPacked(x,g))=ntsInput(x) %(nt_source_definition)%
  . ntOutput(ntPacked(x,g))=ntMachineOutput(ntsMachine(x)) %(nt_output_definition)%
  . ntClock(ntPacked(x,g))=ntsClock(x) %(nt_clock_record_definition)%
  . ntEnabled(ntPacked(x,g)) <=> ntLiveMachine(ntsMachine(x)) %(nt_enabled_definition)%
  . ntHalted(ntPacked(x,g)) <=> ntHaltMachine(ntsMachine(x)) %(nt_halted_definition)%
  . ntStart(c)=ntPacked(ntSourceRecord(c,ntInitialMachine(c),ntHNil,vZ),ntE) %(nt_initial_definition)%
  forall x : NTSourceRecord; z : NTNativeState; g : NTFrame
  . ntDecodeState(ntEncodeState(x,g))=x %(nt_full_original_state_roundtrip)% %implied
  . ntEncodeState(ntDecodeState(z),ntFrame(z))=z %(nt_full_native_state_roundtrip)% %implied
  . ntDecodeState(ntStep(ntEncodeState(x,g)))=ntTick(x) %(nt_same_actual_source_step)% %implied
  . ntUndo(ntTick(x))=x %(nt_history_returns_the_whole_original_state)% %implied
  . ntSource(ntStep(z))=ntSource(z) %(nt_tick_retains_original_input)% %implied
  . ntClock(ntStep(z))=vS(ntClock(z)) %(nt_tick_is_one_actual_original_tick)% %implied
  forall c : VInput
  . ntSource(ntStart(c))=c %(nt_initial_retains_original_input)% %implied
  . ntClock(ntStart(c))=vZ %(nt_initial_clock_zero)% %implied
  forall q : RGTriple
  . rgFredkin(rgFredkin(q))=q %(nt_operational_fredkin_original_wires)% %implied
  . rgToffoli(rgToffoli(q))=q %(nt_operational_toffoli_original_wires)% %implied
end

spec NativeClockTorserRun = NativeClockTorserState then
  free type NTProof ::= ntIdentity(NTNativeState) | ntPrimitive(NTNativeState) |
                        ntCompose(NTProof;NTProof) | ntReexpress(NTProof) |
                        ntClose(NTProof;RReceipt)
  ops ntBegin,ntEnd : NTProof -> NTNativeState;
      ntWork : NTProof -> VNat;
      ntEncodeRun,ntDecodeRun : NTProof -> NTProof
  preds ntValid : NTProof;
        ntJudgment : VInput * NTNativeState * NTProof * VNat * NTNativeState;
        ntRunInvariant : NTProof
  forall x : NTNativeState; p,q : NTProof; h : RReceipt
  . ntBegin(ntIdentity(x))=x %(nt_identity_begin)%
  . ntEnd(ntIdentity(x))=x %(nt_identity_end)%
  . ntWork(ntIdentity(x))=vZ %(nt_identity_work)%
  . ntValid(ntIdentity(x)) %(nt_identity_rule)%
  . ntBegin(ntPrimitive(x))=x %(nt_primitive_begin)%
  . ntEnd(ntPrimitive(x))=ntStep(x) %(nt_primitive_end)%
  . ntWork(ntPrimitive(x))=vS(vZ) %(nt_primitive_work)%
  . ntValid(ntPrimitive(x)) <=> ntEnabled(x) %(nt_actual_tick_rule)%
  . ntBegin(ntCompose(p,q))=ntBegin(p) %(nt_compose_begin)%
  . ntEnd(ntCompose(p,q))=ntEnd(q) %(nt_compose_end)%
  . ntWork(ntCompose(p,q))=cdAdd(ntWork(p),ntWork(q)) %(nt_costed_composition_work)%
  . ntValid(ntCompose(p,q)) <=> ntValid(p) /\ ntValid(q) /\ ntEnd(p)=ntBegin(q) %(nt_costed_composition_rule)%
  . ntBegin(ntReexpress(p))=ntBegin(p) %(nt_presentation_begin)%
  . ntEnd(ntReexpress(p))=ntEnd(p) %(nt_presentation_end)%
  . ntWork(ntReexpress(p))=ntWork(p) %(nt_presentation_no_executed_operation)%
  . ntValid(ntReexpress(p)) <=> ntValid(p) %(nt_pure_presentation_rule)%
  . ntBegin(ntClose(p,h))=ntBegin(p) %(nt_terminal_begin)%
  . ntEnd(ntClose(p,h))=ntEnd(p) %(nt_terminal_end)%
  . ntWork(ntClose(p,h))=ntWork(p) %(nt_terminal_proof_no_hidden_execution)%
  . ntValid(ntClose(p,h)) <=> ntValid(p) /\ ntHalted(ntEnd(p)) /\
       ntOutput(ntEnd(p))=rrEmit(ntSource(ntEnd(p)),h) /\
       rrOK(ntSource(ntEnd(p)),vNil,vWidth(ntSource(ntEnd(p))),h) %(nt_terminal_original_receipt_rule)%
  . ntEncodeRun(p)=p %(nt_run_codec_retains_complete_proof)%
  . ntDecodeRun(p)=p %(nt_run_decoder_retains_complete_proof)%
  %% These identities are on the already-native free NTProof syntax. They
  %% retain its original run packet; they are not a new computational encoder.
  . ntRunInvariant(p) <=> (ntValid(p) =>
       ntSource(ntEnd(p))=ntSource(ntBegin(p)) /\
       ntClock(ntEnd(p))=cdAdd(ntClock(ntBegin(p)),ntWork(p))) %(nt_complete_run_invariant_definition)%
  forall c : VInput; x,y : NTNativeState; p : NTProof; k : VNat
  . ntJudgment(c,x,p,k,y) <=> ntValid(p) /\ ntBegin(p)=x /\ ntEnd(p)=y /\
       ntWork(p)=k /\ ntSource(x)=c %(nt_named_native_judgment_definition)%
  %% Standard natural arithmetic interpreted by the inherited free VNat.
  forall a,b,c : VNat
  . cdAdd(cdAdd(a,b),c)=cdAdd(a,cdAdd(b,c)) %(nt_nat_associativity_interpretation)%
  %% This is structural induction for the explicitly free NTProof syntax.
  . ((forall x : NTNativeState . ntRunInvariant(ntIdentity(x))) /\
     (forall x : NTNativeState . ntRunInvariant(ntPrimitive(x))) /\
     (forall p,q : NTProof . ntRunInvariant(p) /\ ntRunInvariant(q) => ntRunInvariant(ntCompose(p,q))) /\
     (forall p : NTProof . ntRunInvariant(p) => ntRunInvariant(ntReexpress(p))) /\
     (forall p : NTProof; h : RReceipt . ntRunInvariant(p) => ntRunInvariant(ntClose(p,h)))) =>
       (forall p : NTProof . ntRunInvariant(p)) %(nt_free_execution_proof_induction)%
  forall x : NTNativeState; p,q : NTProof; h : RReceipt
  . ntRunInvariant(ntIdentity(x)) %(nt_clock_identity_case)% %implied
  . ntRunInvariant(ntPrimitive(x)) %(nt_clock_actual_tick_case)% %implied
  . ntRunInvariant(p) /\ ntRunInvariant(q) => ntRunInvariant(ntCompose(p,q)) %(nt_clock_composition_case)% %implied
  . ntRunInvariant(p) => ntRunInvariant(ntReexpress(p)) %(nt_clock_presentation_case)% %implied
  . ntRunInvariant(p) => ntRunInvariant(ntClose(p,h)) %(nt_clock_terminal_case)% %implied
  . ntRunInvariant(p) %(nt_complete_original_clock_invariant)% %implied
  . ntDecodeRun(ntEncodeRun(p))=p %(nt_complete_run_packet_return)% %implied
  . ntWork(ntEncodeRun(p))=ntWork(p) %(nt_run_transport_retains_actual_bit_work)% %implied
end

spec NativeClockH24Rules = NativeClockTorserRun then
  sort NTReserve
  ops ntPhi,ntSlack : NTReserve * NTNativeState -> VNat
  preds ntReserveTick,ntTightTick : NTReserve * NTNativeState;
        ntNativeMinimum : VInput * VWord * VNat
  forall e : NTReserve; x : NTNativeState
  . ntReserveTick(e,x) <=>
       cdAdd(vS(vZ),cdAdd(ntPhi(e,ntStep(x)),ntSlack(e,x)))=ntPhi(e,x) %(nt_upper_reserve_rule_definition)%
  . ntTightTick(e,x) <=> ntReserveTick(e,x) /\ ntSlack(e,x)=vZ %(nt_tight_reserve_definition)%
  . ntReserveTick(e,x) =>
       ncMMul(ncClock(vS(vZ)),ncMMul(ncClock(ntPhi(e,ntStep(x))),ncClock(ntSlack(e,x))))=ncClock(ntPhi(e,x))
       %(nt_upper_reserve_has_exact_native_clock_equation)% %implied
  . ntTightTick(e,x) => cdAdd(vS(vZ),ntPhi(e,ntStep(x)))=ntPhi(e,x)
       %(nt_tight_tick_consumes_exactly_one_original_unit)% %implied
  forall c : VInput; w : VWord; k : VNat
  . ntNativeMinimum(c,w,k) <=> (exists p : NTProof; h : RReceipt .
       ntValid(ntClose(p,h)) /\ ntBegin(p)=ntStart(c) /\ ntOutput(ntEnd(p))=w /\ ntWork(p)=k)
       %(nt_terminal_native_minimum_definition)%
  forall p : NTProof; h : RReceipt
  . ntValid(ntClose(p,h)) => vShortest(ntSource(ntEnd(p)),ntOutput(ntEnd(p)))
       %(nt_terminal_rule_constructs_original_verifier_minimum)% %implied
  forall c : VInput; w : VWord; k : VNat
  . ntNativeMinimum(c,w,k) => vShortest(c,w) %(nt_native_minimum_returns_all_original_competitors)% %implied
  . ntNativeMinimum(c,w,k) =>
       (vPositiveTag(w) <=> (exists a : VWord . vModel(c,a)))
       %(nt_native_terminal_tag_returns_original_sat)% %implied
  . ntNativeMinimum(c,vFallback(c),k) => vRefuted(c)
       %(nt_native_minimum_reference_returns_original_refutation)% %implied
end
''')
put(r'''
%% Portable full-class interface. This does not assert either target inhabited.
%% One source machine and a,d are chosen before every original encoded CNF.
spec NativeClockUniformTarget = NativeClockH24Rules then
  free type NTMonitor ::= ntMonitor(CDMachine)
  ops ntDecodeMonitor : NTMonitor -> CDMachine
  preds ntNativeEmit : NTMonitor * VInput * VNat;
        ntUniformNativePass : NTMonitor * VNat * VNat;
        ntNativeByClock : NTMonitor * VInput * VNat * VNat;
        ntWholeNativeClock : ()
  forall u : NTMonitor
  . exists m : CDMachine . u=ntMonitor(m) %(nt_monitor_constructor_cases)%
  forall m : CDMachine; c : VInput; t,a,d : VNat
  . ntDecodeMonitor(ntMonitor(m))=m %(nt_monitor_decode_definition)%
  . ntNativeEmit(ntMonitor(m),c,t) <=> cdEmit(m,c,t) %(nt_monitor_same_original_hit_and_tick)%
  forall u : NTMonitor; c : VInput; a,d : VNat
  . ntNativeByClock(u,c,a,d) <=>
       (exists t : VNat . vLe(t,cdBudget(c,a,d)) /\ ntNativeEmit(u,c,t))
       %(nt_native_by_frozen_clock_definition)%
  . ntUniformNativePass(u,a,d) <=>
       ((forall f : VInput; t : VNat . cdInput3(f) /\ ntNativeEmit(u,f,t) => vRefuted(f)) /\
        (forall f : VInput . cdInput3(f) /\ vRefuted(f) => ntNativeByClock(u,f,a,d)))
       %(nt_uniform_native_target_full_quantifiers)%
  . ntWholeNativeClock <=> (exists u : NTMonitor; a,d : VNat . ntUniformNativePass(u,a,d))
       %(nt_whole_native_clock_definition)%
  forall m : CDMachine; c : VInput; a,d : VNat
  . ntNativeByClock(ntMonitor(m),c,a,d) <=> cdStopYes(m,c,a,d)
       %(nt_native_deadline_is_same_original_deadline)% %implied
  . ntUniformNativePass(ntMonitor(m),a,d) <=> cdPass(m,a,d)
       %(nt_full_class_same_machine_same_clock)% %implied
  . ntUniformNativePass(ntMonitor(m),a,d) /\ cdInput3(c) =>
       (ntNativeByClock(ntMonitor(m),c,a,d) <=> vRefuted(c))
       %(nt_uniform_native_clock_decides_original_negative)% %implied
  . ntWholeNativeClock <=> (exists m : CDMachine; a,d : VNat . cdPass(m,a,d))
       %(nt_whole_quantified_bridge_returns_to_original_source)% %implied
  . ntWholeNativeClock <=>
       (exists m : CDMachine; a,d : VNat . cdSound(m) /\ cdStopsCorrectly(m,a,d))
       %(nt_native_whole_clock_iff_original_stopped_decider)% %implied
end
''')
(D/'Native_Clock_Torser.het').write_text('\n'.join(parts))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
parents=[p for p in [source,old/'TORSOR_MODEL.md',old/'algebra/noncommutative_native.py',old/'algebra/torsor_matrix.py',B/'h24_agent_native/originals/Belnap_Cech_Cayley_Original_Return.het'] if p.exists()]
(D/'SOURCE_MAP.json').write_text(json.dumps({'new_construction':'Native clock and shortest-verifier torser judgment','parent_sources':[{'path':str(p),'sha256':sha(p)} for p in parents],'formal_file':str(D/'Native_Clock_Torser.het'),'formal_sha256':sha(D/'Native_Clock_Torser.het'),'imports':['Native_Shortest_Proof.FixedMonitorClock','Native_Shortest_Proof.NativeRootMatrix','Native_Shortest_Proof.CechReversibleGates'],'explicit_interpretation_laws':['Associative coefficient ring with involution and odd third','Natural embedding in characteristic zero; order stays on source VNat','Ordinary finite matrix algebra and concrete Gram inverse','Actual local finite event restores the previous machine state','Structural induction on free execution-proof syntax','Source natural-addition associativity'],'target_existence_assumptions':[]},indent=2)+'\n')
print(D/'Native_Clock_Torser.het')
