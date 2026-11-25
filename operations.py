"""Typed operation registry and replay gate. Python-call interface, not untrusted string eval.
The claimed result is recomputed from its actual inputs; a naked receipt is never sufficient.
"""
from dataclasses import dataclass
from typing import Any
import invariants as i

# Closed list of implemented operation constructors. Registration of new external
# theorems must not be achieved merely by adding a name with a True return.
OPS={
 'persistent_mode':i.persistent_mode, 'stationary_observation':i.stationary_observation,
 'history':i.history, 'covariance':i.covariance, 'locality':i.locality,
 'winding':i.winding, 'winding_alias':i.winding_alias, 'scale_identification':i.scale_identification,
 'gap_claim':i.gap_claim, 'uniform_gap_counterexample':i.uniform_gap_counterexample,
 'finite_clock_ccr':i.finite_clock_ccr, 'dyadic_zero_claim':i.dyadic_zero_claim,
 'dyadic_gram_claim':i.dyadic_gram_claim, 'projector_involution':i.projector_involution,
 'posterior':i.posterior, 'independent_evidence_claim':i.independent_evidence_claim,
 'moment_sufficiency_claim':i.moment_sufficiency_claim, 'residual_expansion':i.residual_expansion,
 'check_trace':i.check_trace, 'claim_universal_clock':i.claim_universal_clock,
 'physical_external':i.physical_external, 'finite_perfect_clock':i.finite_perfect_clock,
 'two_level_orthogonal':i.two_level_orthogonal, 'vacuum_flux':i.vacuum_flux,
 'classical_energy_floor':i.classical_energy_floor, 'boundary_charge':i.boundary_charge,
 'clock_no_hit':i.clock_no_hit, 'bool_diagonal':i.bool_diagonal,
 'no_work_from_identity':i.no_work_from_identity, 'haar_owner_integral':i.haar_owner_integral,
 'symmetric_input':i.symmetric_input, 'six_frame_integral_haar':i.six_frame_integral_haar,
 'finite_observation_clock_alias':i.finite_observation_clock_alias,
 'empty_ground_from_reflection':i.empty_ground_from_reflection,
}
@dataclass(frozen=True)
class Claim:
    operation: str
    arguments: tuple[Any,...]
@dataclass(frozen=True)
class OperationProof:
    claim: Claim
    certificate: i.Receipt

def evaluate(claim:Claim)->i.Receipt:
    if claim.operation not in OPS:
        return i.opn('OPERATION.UNREGISTERED','closed operation registry',claim.operation)
    try:
        return OPS[claim.operation](*claim.arguments)
    except (ValueError,TypeError,AttributeError,KeyError,IndexError,ZeroDivisionError) as e:
        return i.opn('OPERATION.ILL_TYPED','closed operation registry',claim.operation,str(e))

def prove(claim:Claim)->OperationProof:
    return OperationProof(claim,evaluate(claim))

def replay(claim:Claim,proof:OperationProof)->bool:
    """Use the caller's ACTUAL claim; do not trust the certificate's scope or status."""
    return claim==proof.claim and evaluate(claim)==proof.certificate

def accepts(claim:Claim,proof:OperationProof,expected:i.Status)->bool:
    # OPEN cannot authorize a witness or counterexample.
    return expected in (i.Status.PROVED,i.Status.REFUTED) and replay(claim,proof) and proof.certificate.status==expected
