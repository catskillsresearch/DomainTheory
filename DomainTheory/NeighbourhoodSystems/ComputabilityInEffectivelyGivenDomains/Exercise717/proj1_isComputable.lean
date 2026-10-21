/-ai
The second projection is a computable endomap of the sharp presentation.

By the index characterization, the relation holds when the target code is zero, or the source code is even and nonzero and the sharp neighbourhood of the right component of its halved predecessor is contained in the target neighbourhood. Equality with zero, evenness, and inequality with zero are recursively decidable, and the reindexed inclusion is decidable by composing the inclusion decider with that primitive-recursive reindexing. The resulting disjunction is decidable, hence recursively enumerable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1_rel_Vsharp_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Exercise 7.17 (Scott 1981, PRG-19) — `proj₁` is computable.**
`V_m proj₁ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{q(m/2-1)} ⊆ V_k)`: a disjunction of the equality and
inclusion deciders with primitive-recursive parity/right-child reindexings, hence r.e. -/
theorem proj1_isComputable (P : ComputablePresentation D) :
    IsComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj1Map hD) := by
  show REPred (fun s => (proj1Map hD).rel (Vsharp D P s.unpair.1) (Vsharp D P s.unpair.2))
  have hk0 : RecDecidable (fun s => s.unpair.2 = 0) :=
    RecDecidable.natEq Nat.Primrec.right (Nat.Primrec.const 0)
  have hmod : RecDecidable (fun s => s.unpair.1 % 2 = 0) :=
    RecDecidable.natEq (primrec_mod2.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hne : RecDecidable (fun s => s.unpair.1 ≠ 0) :=
    (RecDecidable.natEq Nat.Primrec.left (Nat.Primrec.const 0)).not
  have hg : Nat.Primrec (fun s => Nat.pair (s.unpair.1 / 2 - 1).unpair.2 s.unpair.2) :=
    (Nat.Primrec.right.comp (primrec_sub₂ (primrec_div2.comp Nat.Primrec.left)
      (Nat.Primrec.const 1))).pair Nat.Primrec.right
  have hincl : RecDecidable (fun s => Vsharp D P (s.unpair.1 / 2 - 1).unpair.2 ⊆
      Vsharp D P s.unpair.2) := by
    refine RecDecidable.of_iff (fun s => ?_) ((dsharpPresentation P hD).incl_computable.comp hg)
    simp only [dsharpPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact (RecDecidable.of_iff (fun s => proj1_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2)
    (hk0.or (hmod.and (hne.and hincl)))).re

end Proposition77
end DomainTheory.NeighbourhoodSystems
