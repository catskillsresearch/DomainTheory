/-ai
Membership in the numerical evaluator is uniformly recursively enumerable. The predicate that the second component of a pair lies in the value of the evaluator at the first component is recursively enumerable.

Well-formedness of a trace conjoined with recording of the two components of a pair is recursively enumerable, by composing the recursively enumerable well-formedness predicate with the second projection and the primitive recursive recording relation with the two projections. Decoding a natural number as a trace, with the empty trace as default, preserves recursive enumerability. Existential quantification over that code, transported along encoding and decoding, is the existence of a well-formed recording trace. The membership criterion for the evaluator identifies that existence with the stated predicate.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_iff
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecRel_valTraceHas
public import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_re

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


/-- Uniform r.e. membership in `val`. -/
theorem valNat_mem_re : REPred fun q : ℕ × ℕ => q.2 ∈ valNat q.1 := by
  have htr : REPred fun q : (ℕ × ℕ) × ValTrace =>
      valTraceOk q.2 ∧ valTraceHas q.2 q.1.1 q.1.2 :=
    REPred.and (valTraceOk_re.comp Computable.snd)
      ((primrecRel_valTraceHas.comp Primrec.snd Primrec.fst).computablePred.to_re)
  have hN : REPred fun q : (ℕ × ℕ) × ℕ =>
      valTraceOk ((decode q.2 : Option ValTrace).getD []) ∧
        valTraceHas ((decode q.2).getD []) q.1.1 q.1.2 :=
    htr.comp (Computable.pair Computable.fst
      (Computable.option_getD (Computable.decode.comp Computable.snd)
        (Computable.const [])))
  have hex : REPred fun q : ℕ × ℕ =>
      ∃ tr, valTraceOk tr ∧ valTraceHas tr q.1 q.2 :=
    _root_.REPred.of_eq
      (REPred.exists_param (α := ℕ × ℕ)
        (p := fun q enc =>
          valTraceOk ((decode enc : Option ValTrace).getD []) ∧
            valTraceHas ((decode enc).getD []) q.1 q.2)
        hN)
      fun q =>
      ⟨fun ⟨enc, henc⟩ => ⟨(decode enc).getD [], henc⟩, fun ⟨tr, hok⟩ =>
        ⟨encode tr, by simpa [encodek] using hok⟩⟩
  exact _root_.REPred.of_eq hex fun q => (valNat_mem_iff q.1 q.2).symm

end DomainTheory.DataTypesAsLattices
