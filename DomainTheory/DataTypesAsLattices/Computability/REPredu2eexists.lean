module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsComputable
public import DomainTheory.DataTypesAsLattices.Computability.LambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj4
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.Realizes2
public import DomainTheory.DataTypesAsLattices.Computability.composeC
public import DomainTheory.DataTypesAsLattices.Computability.constComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Computability.addStepC
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.safePredC
public import DomainTheory.DataTypesAsLattices.Computability.subStepC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.pairTerm
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter
public import DomainTheory.DataTypesAsLattices.Computability.sqrtEnv
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepTerm
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSquareTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairDeltaTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairTestTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpEnv
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpTerm
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer
public import DomainTheory.DataTypesAsLattices.Computability.precEnv
public import DomainTheory.DataTypesAsLattices.Computability.precTerm
public import DomainTheory.DataTypesAsLattices.Computability.precC
public import DomainTheory.DataTypesAsLattices.Computability.enumFun
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC
public import DomainTheory.DataTypesAsLattices.Computability.ComputableFin
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Projection of an r.e. binary predicate, by dovetailing `Code.evaln`. -/
theorem REPred.exists {p : ℕ → ℕ → Prop}
    (hp : REPred fun q : ℕ × ℕ => p q.1 q.2) :
    REPred fun n => ∃ m, p n m := by
  have hnat : Nat.Partrec fun k : ℕ =>
      Part.bind (decode₂ (ℕ × ℕ) k) fun q : ℕ × ℕ =>
        (Part.assert (p q.1 q.2) fun _ => Part.some ()).map encode :=
    (Partrec.bind_decode₂_iff
      (f := fun q : ℕ × ℕ => Part.assert (p q.1 q.2) fun _ => Part.some ())).mp hp
  obtain ⟨c, hc⟩ := Code.exists_code.mp hnat
  have hfn : Computable₂ fun n k : ℕ =>
      (evaln k.unpair.2 c (encode (n, k.unpair.1))).map fun _ : ℕ => () := by
    refine (Primrec.option_map ?_ (Primrec.const ()).to₂).to_comp
    exact primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
          (Primrec.const c))
        (Primrec.encode.comp
          (Primrec.pair Primrec.fst
            (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
  have hr : REPred fun n =>
      (Nat.rfindOpt fun k =>
        (evaln k.unpair.2 c (encode (n, k.unpair.1))).map fun _ : ℕ => ()).Dom :=
    Partrec.dom_re (Partrec.rfindOpt hfn)
  refine _root_.REPred.of_eq hr fun n => ?_
  constructor
  · intro hdom
    rw [Nat.rfindOpt_dom] at hdom
    obtain ⟨k, u, hu⟩ := hdom
    cases hopt : evaln k.unpair.2 c (encode (n, k.unpair.1)) with
    | none =>
      rw [hopt] at hu
      cases hu
    | some val =>
      have hin : val ∈ evaln k.unpair.2 c (encode (n, k.unpair.1)) := by
        rw [hopt]; rfl
      have hsound : val ∈ Code.eval c (encode (n, k.unpair.1)) :=
        evaln_sound hin
      rw [hc] at hsound
      rw [Part.mem_bind_iff] at hsound
      obtain ⟨q, hq, hv⟩ := hsound
      have hqe : decode₂ (ℕ × ℕ) (encode (n, k.unpair.1)) = some q := by
        simpa using hq
      have hq' : q = (n, k.unpair.1) :=
        Option.some_inj.mp (hqe.symm.trans (decode₂_encode (n, k.unpair.1)))
      subst hq'
      rw [Part.mem_map_iff] at hv
      obtain ⟨u, hu, _⟩ := hv
      exact ⟨k.unpair.1, (Part.mem_assert_iff.mp hu).1⟩
  · intro ⟨m, hm⟩
    have hmem : encode () ∈ Code.eval c (encode (n, m)) := by
      rw [hc, Part.mem_bind_iff]
      refine ⟨(n, m), ?_, ?_⟩
      · rw [decode₂_encode]
        exact Part.mem_some_iff.mpr rfl
      · rw [Part.mem_map_iff]
        exact ⟨(), Part.mem_assert_iff.mpr ⟨hm, Part.mem_some_iff.mpr rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := evaln_complete.mp hmem
    have hs' : evaln s c (Nat.pair n m) = some (encode ()) := hs
    refine (Nat.rfindOpt_dom (f := fun k =>
      (evaln k.unpair.2 c (encode (n, k.unpair.1))).map fun _ => ())).mpr
      ⟨Nat.pair m s, (), ?_⟩
    simp [Nat.unpair_pair, hs']

end DomainTheory.DataTypesAsLattices
