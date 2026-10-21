/-ai
If some sharp neighbourhood lies in the intersection of the sharp neighbourhoods of i and j, then the intersection index carried by the course-of-values value of the sharp decider step denotes that intersection, assuming only that the intersection function of D is correct on consistent pairs and that every neighbourhood of D is nonempty.

The argument is strong induction on the pair code. A zero on the left returns j, and the intersection with the master neighbourhood is the other neighbourhood. A leaf or a node against zero returns that leaf or node. Two leaves reduce to D's intersection after the odd-odd intersection and the characterization of a sub-embedding of a leaf. A leaf against a node, or a node against a leaf, has empty intersection, so the witness contradicts nonemptiness. Two nodes have strictly smaller child pairs; the memo table returns the earlier values, and the intersection index is the node embedding of the two inductive intersection indices.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.unpair_fst_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.nat_shape
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.pair_lt_pair_of_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf_def
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_i0
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_j0
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_ll
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep_nn

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **Intersection-index correctness in isolation.** The `intI` component of `gOf (dsharpStep …)` is
independent of the `eq`/`cons` bits (`fcons`/`feq`), so it is correct assuming only that `finter`
correctly intersects in `D`. This lets the `inter` *data* field be built with dummy `fcons`/`feq`
while staying choice-free. -/
theorem dsharp_intI_correct (hD : ∀ X, D.mem X → X.Nonempty)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b) :
    ∀ i j : ℕ, (∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
      Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
        = Vsharp D P i ∩ Vsharp D P j := by
  have key : ∀ w : ℕ, ∀ i j : ℕ, Nat.pair i j = w →
      (∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
      Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
        = Vsharp D P i ∩ Vsharp D P j := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro i j hw
      rcases nat_shape i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · intro _
        simp only [gOf_def]; rw [dsharpStep_i0 fcons feq finter j]
        simp only [intI_packT]; rw [Vsharp_zero_inter P]
      · rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · intro _
          simp only [gOf_def]; rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 1 ≠ 0)]
          simp only [intI_packT]; exact (Vsharp_inter_zero P (2 * a + 1)).symm
        · intro hp
          simp only [gOf_def]; rw [dsharpStep_ll fcons feq finter a b]
          simp only [intI_packT]
          rw [Vsharp_odd_inter_odd P] at hp ⊢
          rw [exists_sub_embZero_iff P hD] at hp
          rw [Vsharp_odd P, hinter a b hp]
        · intro hp
          exfalso
          rw [Vsharp_odd_inter_even P] at hp
          obtain ⟨l, hl⟩ := hp
          obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
          exact absurd (hl hx) (by simp)
      · rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · intro _
          simp only [gOf_def]; rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 2 ≠ 0)]
          simp only [intI_packT]; exact (Vsharp_inter_zero P (2 * a + 2)).symm
        · intro hp
          exfalso
          rw [Vsharp_even_inter_odd P] at hp
          obtain ⟨l, hl⟩ := hp
          obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
          exact absurd (hl hx) (by simp)
        · intro hp
          have hlt1 : Nat.pair a.unpair.1 b.unpair.1 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_fst_le a; omega) (by have := unpair_fst_le b; omega)
          have hlt2 : Nat.pair a.unpair.2 b.unpair.2 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_snd_le a; omega) (by have := unpair_snd_le b; omega)
          have hr1 := listGet_rtbl (dsharpStep fcons feq finter) hlt1
          have hr2 := listGet_rtbl (dsharpStep fcons feq finter) hlt2
          rw [Vsharp_even_inter_even P] at hp ⊢
          rw [exists_sub_embPair_iff P hD] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [gOf_def]; rw [dsharpStep_nn fcons feq finter a b]
          simp only [intI_packT]; rw [hr1, hr2, Vsharp_even P]
          simp only [unpair_pair_fst, unpair_pair_snd]
          rw [ih _ (hw ▸ hlt1) a.unpair.1 b.unpair.1 rfl hp1,
              ih _ (hw ▸ hlt2) a.unpair.2 b.unpair.2 rfl hp2]
  intro i j; exact key (Nat.pair i j) i j rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
