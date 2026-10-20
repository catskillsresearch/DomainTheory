module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.unpair_fst_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.nat_shape
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.pair_lt_pair_of_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_inter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd_inter_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd_inter_even
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even_inter_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even_inter_even
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.exists_sub_embZero_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.exists_sub_embPair_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_eq_Gamma_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_i0
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_j0
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_ll
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_ln
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_nl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_nn

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharp_decider_spec (hD : ∀ X, D.mem X → X.Nonempty)
    (hcons : ∀ a b, fcons (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b)
    (heq : ∀ a b, feq (Nat.pair a b) = 1 ↔ P.X a = P.X b)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b) :
    ∀ i j : ℕ,
      (consB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ ∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) ∧
        ((∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
          Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
            = Vsharp D P i ∩ Vsharp D P j) ∧
        (eqB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ Vsharp D P i = Vsharp D P j) := by
  have key : ∀ w : ℕ, ∀ i j : ℕ, Nat.pair i j = w →
      (consB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ ∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) ∧
        ((∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
          Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
            = Vsharp D P i ∩ Vsharp D P j) ∧
        (eqB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ Vsharp D P i = Vsharp D P j) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro i j hw
      rcases nat_shape i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · -- i = 0 (Γ ∩ V_j = V_j)
        simp only [gOf_def]
        rw [dsharpStep_i0 fcons feq finter j]
        simp only [eqB_packT, consB_packT, intI_packT]
        refine ⟨?_, ?_, ?_⟩
        · exact ⟨fun _ => ⟨j, (Vsharp_zero_inter P j).ge⟩, fun _ => trivial⟩
        · intro _; rw [Vsharp_zero_inter P]
        · constructor
          · intro h
            have hj : j = 0 := by omega
            rw [hj]
          · intro h
            have hj : j = 0 := (Vsharp_eq_Gamma_iff P hD j).mp (h.symm.trans (Vsharp_zero P))
            omega
      · -- i = 2a+1 (leaf)
        rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- j = 0
          simp only [gOf_def]
          rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 1 ≠ 0)]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨fun _ => ⟨2 * a + 1, (Vsharp_inter_zero P (2 * a + 1)).ge⟩, fun _ => trivial⟩
          · intro _; exact (Vsharp_inter_zero P (2 * a + 1)).symm
          · rw [Vsharp_zero P, Vsharp_eq_Gamma_iff P hD]; omega
        · -- j = 2b+1 (leaf ∩ leaf)
          simp only [gOf_def]
          rw [dsharpStep_ll fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_odd_inter_odd P, exists_sub_embZero_iff P hD]; exact hcons a b
          · intro hp
            rw [Vsharp_odd_inter_odd P] at hp ⊢
            rw [exists_sub_embZero_iff P hD] at hp
            rw [Vsharp_odd P, hinter a b hp]
          · rw [Vsharp_odd P, Vsharp_odd P, heq a b]
            exact ⟨fun h => by rw [h], fun h => embZero_injective h⟩
        · -- j = 2b+2 (leaf ∩ node : inconsistent)
          simp only [gOf_def]
          rw [dsharpStep_ln fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_odd_inter_even P]
            constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨l, hl⟩
              obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
              exact absurd (hl hx) (by simp)
          · rw [Vsharp_odd_inter_even P]
            rintro ⟨l, hl⟩
            obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
            exact absurd (hl hx) (by simp)
          · rw [Vsharp_odd P, Vsharp_even P]
            constructor
            · intro h; exact absurd h (by decide)
            · intro h; exact absurd h (embZero_ne_embPair D hD (P.mem_X a) _ _)
      · -- i = 2a+2 (node)
        rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- j = 0
          simp only [gOf_def]
          rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 2 ≠ 0)]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨fun _ => ⟨2 * a + 2, (Vsharp_inter_zero P (2 * a + 2)).ge⟩, fun _ => trivial⟩
          · intro _; exact (Vsharp_inter_zero P (2 * a + 2)).symm
          · rw [Vsharp_zero P, Vsharp_eq_Gamma_iff P hD]; omega
        · -- j = 2b+1 (node ∩ leaf : inconsistent)
          simp only [gOf_def]
          rw [dsharpStep_nl fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_even_inter_odd P]
            constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨l, hl⟩
              obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
              exact absurd (hl hx) (by simp)
          · rw [Vsharp_even_inter_odd P]
            rintro ⟨l, hl⟩
            obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
            exact absurd (hl hx) (by simp)
          · rw [Vsharp_even P, Vsharp_odd P]
            constructor
            · intro h; exact absurd h (by decide)
            · intro h; exact absurd h.symm (embZero_ne_embPair D hD (P.mem_X b) _ _)
        · -- j = 2b+2 (node ∩ node : recurse)
          have hlt1 : Nat.pair a.unpair.1 b.unpair.1 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_fst_le a; omega) (by have := unpair_fst_le b; omega)
          have hlt2 : Nat.pair a.unpair.2 b.unpair.2 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_snd_le a; omega) (by have := unpair_snd_le b; omega)
          have hr1 := listGet_rtbl (dsharpStep fcons feq finter) hlt1
          have hr2 := listGet_rtbl (dsharpStep fcons feq finter) hlt2
          obtain ⟨ihc1, ihi1, ihe1⟩ :=
            ih (Nat.pair a.unpair.1 b.unpair.1) (hw ▸ hlt1) a.unpair.1 b.unpair.1 rfl
          obtain ⟨ihc2, ihi2, ihe2⟩ :=
            ih (Nat.pair a.unpair.2 b.unpair.2) (hw ▸ hlt2) a.unpair.2 b.unpair.2 rfl
          simp only [gOf_def]
          rw [dsharpStep_nn fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          rw [hr1, hr2]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_even_inter_even P, exists_sub_embPair_iff P hD, nat_mul_eq_one]
            exact and_congr ihc1 ihc2
          · intro hp
            rw [Vsharp_even_inter_even P] at hp ⊢
            rw [exists_sub_embPair_iff P hD] at hp
            obtain ⟨hp1, hp2⟩ := hp
            rw [Vsharp_even P]
            simp only [unpair_pair_fst, unpair_pair_snd]
            rw [ihi1 hp1, ihi2 hp2]
          · rw [Vsharp_even P, Vsharp_even P, nat_mul_eq_one, ihe1, ihe2]
            constructor
            · rintro ⟨h1, h2⟩; rw [h1, h2]
            · intro h; exact embPair_injective h
  intro i j
  exact key (Nat.pair i j) i j rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
