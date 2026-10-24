module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gEval
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_dom
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_cod
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.embZero_ne_embPair_of_memS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_gamma_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_embZero_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_embPair_inv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_interRight
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.primrec_gStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gEval_sound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gEval_complete

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **Exercise 7.17 (Part 2) (Scott 1981, PRG-19).** If `E` is effectively given (presentation `Q`) and
`u : D → E`, `v : E × E → E` are computable, then the unique strict catamorphism `g : D^§ → E`
(`gMap`) is computable.

The index relation `Xₙ g Yₘ = GRel u v (Vₙ)(Yₘ)` is realised as the recursively-enumerable existential
`∃ cert, gEval⟨n,cert⟩.ok = 1 ∧ Y_{cert.out} = Yₘ` over the primitive-recursive certificate evaluator
`gEval`. Soundness (`gEval_sound`) and completeness (`gEval_complete`) of the certificate give the
equivalence; the deciders `fe`/`fU`/`fV` are read off `Q.eq_computable` and the r.e. relations of
`u`/`v`. -/
theorem gMap_isComputable (hD : ∀ X, D.mem X → X.Nonempty)
    (P : ComputablePresentation D) (Q : ComputablePresentation E)
    (hu : ComputableMap P Q u)
    (hv : ComputableMap (prodPresentation Q Q) Q v) :
    ComputableMap (dsharpPresentation P hD) Q (gMap u v hD) := by
  constructor
  obtain ⟨qU, hqU, hqUe⟩ := hu
  obtain ⟨fU, hfUp, hfUe⟩ := hqU
  obtain ⟨qV, hqV, hqVe⟩ := hv
  obtain ⟨fV, hfVp, hfVe⟩ := hqV
  obtain ⟨fe, hfep, hfee⟩ := Q.eq_computable
  have hMidx : Q.X Q.masterIdx = E.master := Q.masterIdx_spec
  have hEq : ∀ m, fe (Nat.pair m Q.masterIdx) = 1 ↔ Q.X m = E.master := by
    intro m
    have h := hfee (Nat.pair m Q.masterIdx)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    rw [hMidx] at h; exact h.symm
  have hU : ∀ a m, (∃ i, fU (Nat.pair i (Nat.pair a m)) = 1) ↔ u.rel (P.X a) (Q.X m) := by
    intro a m
    have h := hqUe (Nat.pair a m)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    rw [h]; exact exists_congr fun i => (hfUe (Nat.pair i (Nat.pair a m))).symm
  have hV : ∀ k1 k2 m, (∃ i, fV (Nat.pair i (Nat.pair (Nat.pair k1 k2) m)) = 1) ↔
      v.rel (prodNbhd (Q.X k1) (Q.X k2)) (Q.X m) := by
    intro k1 k2 m
    have h := hqVe (Nat.pair (Nat.pair k1 k2) m)
    simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd] at h
    rw [h]; exact exists_congr fun i => (hfVe (Nat.pair i (Nat.pair (Nat.pair k1 k2) m))).symm
  -- The certificate body is recursively decidable, hence its existential projection is r.e.
  have hgEval : Nat.Primrec (gEval fe fU fV Q.masterIdx) :=
    primrec_gOf (primrec_gStep fe fU fV Q.masterIdx hfep hfUp hfVp)
  have hidx : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2.unpair.1 s.unpair.1) :=
    (Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left
  have hp1 : RecDecidable (fun s : ℕ =>
      (gEval fe fU fV Q.masterIdx (Nat.pair s.unpair.2.unpair.1 s.unpair.1)).unpair.1 = 1) :=
    ⟨_, Nat.Primrec.left.comp (hgEval.comp hidx), fun _ => Iff.rfl⟩
  have hg2 : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1.unpair.1 s.unpair.2.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hp2 : RecDecidable (fun s : ℕ => Q.X s.unpair.1.unpair.1 = Q.X s.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (Q.eq_computable.comp hg2)
  have hbase : REPred (fun s : ℕ =>
      (gEval fe fU fV Q.masterIdx (Nat.pair s.unpair.2.unpair.1 s.unpair.1)).unpair.1 = 1
        ∧ Q.X s.unpair.1.unpair.1 = Q.X s.unpair.2.unpair.2) := (hp1.and hp2).re
  unfold REPred₂
  refine REPred.of_iff (fun t => ?_) (REPred.proj hbase)
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · intro hg
    obtain ⟨cert, hok, heq⟩ :=
      gEval_complete fe fU fV Q.masterIdx hD P Q hEq hMidx hU hV t.unpair.1 (Q.X t.unpair.2) hg
    exact ⟨cert, hok, heq⟩
  · rintro ⟨cert, hok, heq⟩
    have hsound := gEval_sound fe fU fV Q.masterIdx P Q hEq hU hV t.unpair.1 cert hok
    rw [heq] at hsound
    exact hsound

end Exercise717
end DomainTheory.NeighbourhoodSystems
