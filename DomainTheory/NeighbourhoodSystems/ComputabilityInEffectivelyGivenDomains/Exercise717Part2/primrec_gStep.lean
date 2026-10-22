module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


/-- The certificate step is primitive recursive (when the underlying functions are). -/
theorem primrec_gStep (hfe : Nat.Primrec fe) (hfU : Nat.Primrec fU) (hfV : Nat.Primrec fV) :
    Nat.Primrec (gStep fe fU fV mIdx) := by
  have hw : Nat.Primrec (fun p : ℕ => p.unpair.1) := Nat.Primrec.left
  have htbl : Nat.Primrec (fun p : ℕ => p.unpair.2) := Nat.Primrec.right
  have hnn : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hcert : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hout : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.1) := Nat.Primrec.left.comp hcert
  have hwit : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp hcert)
  have hlc : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp hcert))
  have hrc : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp hcert))
  have hb : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2 - 1) :=
    primrec_sub₂ (primrec_div2.comp hnn) (Nat.Primrec.const 1)
  have hlpos : Nat.Primrec (fun p : ℕ =>
      p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1) :=
    primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1))
      ((Nat.Primrec.left.comp hb).pair hlc)
  have hrpos : Nat.Primrec (fun p : ℕ =>
      p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2) :=
    primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1))
      ((Nat.Primrec.right.comp hb).pair hrc)
  have hchildL : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)) :=
    primrec_listGet₂ htbl hlpos
  have hchildR : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)) :=
    primrec_listGet₂ htbl hrpos
  have hgamma : Nat.Primrec (fun p : ℕ =>
      Nat.pair (fe (Nat.pair p.unpair.1.unpair.2.unpair.1 mIdx)) p.unpair.1.unpair.2.unpair.1) :=
    (hfe.comp (hout.pair (Nat.Primrec.const mIdx))).pair hout
  have hleaf : Nat.Primrec (fun p : ℕ =>
      Nat.pair (fU (Nat.pair p.unpair.1.unpair.2.unpair.2.unpair.1
          (Nat.pair (p.unpair.1.unpair.1 / 2) p.unpair.1.unpair.2.unpair.1)))
        p.unpair.1.unpair.2.unpair.1) :=
    (hfU.comp (hwit.pair ((primrec_div2.comp hnn).pair hout))).pair hout
  have hfVcall : Nat.Primrec (fun p : ℕ =>
      fV (Nat.pair p.unpair.1.unpair.2.unpair.2.unpair.1
        (Nat.pair (Nat.pair
            (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)).unpair.2
            (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)).unpair.2)
          p.unpair.1.unpair.2.unpair.1))) :=
    hfV.comp (hwit.pair
      (((Nat.Primrec.right.comp hchildL).pair (Nat.Primrec.right.comp hchildR)).pair hout))
  have hnode : Nat.Primrec (fun p : ℕ =>
      Nat.pair ((listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)).unpair.1
          * (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)).unpair.1
          * fV (Nat.pair p.unpair.1.unpair.2.unpair.2.unpair.1
              (Nat.pair (Nat.pair
                  (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                    p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)).unpair.2
                  (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                    p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)).unpair.2)
                p.unpair.1.unpair.2.unpair.1)))
        p.unpair.1.unpair.2.unpair.1) :=
    (primrec_mul₂ (primrec_mul₂ (Nat.Primrec.left.comp hchildL) (Nat.Primrec.left.comp hchildR))
      hfVcall).pair hout
  refine (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hnn) hgamma
    (primrec_selectFn (primrec_mod2.comp hnn) hleaf hnode)).of_eq fun p => rfl

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
