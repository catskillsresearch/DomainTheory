module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.proj0_rel_Vsharp_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Proposition 7.7 (Scott 1981, PRG-19) — `proj₀` is computable.**
`V_m proj₀ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{p(m/2-1)} ⊆ V_k)`: a disjunction of the equality and
inclusion deciders with primitive-recursive parity/child reindexings, hence r.e. -/
theorem proj0_isComputable (P : ComputablePresentation D) :
    ComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj0Map hD) := by
  constructor
  show REPred (fun s => (proj0Map hD).rel (Vsharp D P s.unpair.1) (Vsharp D P s.unpair.2))
  have hk0 : RecDecidable (fun s => s.unpair.2 = 0) :=
    RecDecidable.natEq Nat.Primrec.right (Nat.Primrec.const 0)
  have hmod : RecDecidable (fun s => s.unpair.1 % 2 = 0) :=
    RecDecidable.natEq (primrec_mod2.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hne : RecDecidable (fun s => s.unpair.1 ≠ 0) :=
    (RecDecidable.natEq Nat.Primrec.left (Nat.Primrec.const 0)).not
  have hg : Nat.Primrec (fun s => Nat.pair (s.unpair.1 / 2 - 1).unpair.1 s.unpair.2) :=
    (Nat.Primrec.left.comp (primrec_sub₂ (primrec_div2.comp Nat.Primrec.left)
      (Nat.Primrec.const 1))).pair Nat.Primrec.right
  have hincl : RecDecidable (fun s => Vsharp D P (s.unpair.1 / 2 - 1).unpair.1 ⊆
      Vsharp D P s.unpair.2) := by
    refine RecDecidable.of_iff (fun s => ?_) ((dsharpPresentation P hD).incl_computable.comp hg)
    simp only [dsharpPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact (RecDecidable.of_iff (fun s => proj0_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2)
    (hk0.or (hmod.and (hne.and hincl)))).re

end Proposition77
end DomainTheory.NeighbourhoodSystems
