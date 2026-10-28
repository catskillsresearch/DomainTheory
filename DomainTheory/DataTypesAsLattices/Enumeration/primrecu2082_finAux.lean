
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.unionCode
public import DomainTheory.DataTypesAsLattices.Enumeration.botCode
public import DomainTheory.DataTypesAsLattices.Enumeration.finAux
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_num
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec₂_finAux : Primrec fun p : ℕ × ℕ => finAux p.1 p.2 := by
  let step : (ℕ × ℕ) → (ℕ × ℕ) → ℕ := fun p q =>
    if p.1.testBit q.1 then
      applyNat (applyNat unionCode (num q.1)) q.2
    else q.2
  have hstep : Primrec₂ step := by
    unfold step
    have hc : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
        z.1.1.testBit z.2.1 :=
      primrec_testBit.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    have ht : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
        applyNat (applyNat unionCode (num z.2.1)) z.2.2 :=
      primrec_applyNat.comp
        (primrec_applyNat.comp (Primrec.const unionCode)
          (primrec_num.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    have he : Primrec fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact (Primrec.cond hc ht he).to₂.of_eq fun p q => by
      cases h : p.1.testBit q.1 <;> simp
  refine (Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ : ℕ × ℕ => botCode) (h := step)
    Primrec.snd (Primrec.const botCode) hstep).of_eq fun p => ?_
  induction p.2 with
  | zero => rfl
  | succ k ih =>
      change (if p.1.testBit k then
          applyNat (applyNat unionCode (num k))
            (Nat.rec botCode (fun n r => step p (n, r)) k)
        else Nat.rec botCode (fun n r => step p (n, r)) k) =
        finAux p.1 (k + 1)
      rw [finAux, ih]

end DomainTheory.DataTypesAsLattices
