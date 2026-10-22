module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.pairSharp_rel_Vsharp_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Exercise 7.17 (Scott 1981, PRG-19) — the pairing `pair : D^§ × D^§ → D^§` is computable.**
Its index relation is exactly `V_{2·⟨a,b⟩+2} ⊆ V_k`, a recursive slice of `D^§`'s inclusion decider
(`dsharpPresentation.incl_computable`) reindexed by the primitive-recursive node map
`s ↦ ⟨2·(p s)+2, q s⟩`, hence r.e. -/
theorem pairSharp_isComputable (P : ComputablePresentation D) :
    ComputableMap (prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD))
      (dsharpPresentation P hD) (pairSharpMap hD) := by
  constructor
  show REPred (fun s => (pairSharpMap hD).rel
    ((prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD)).X s.unpair.1)
    ((dsharpPresentation P hD).X s.unpair.2))
  have hincl : RecDecidable (fun s => Vsharp D P s.unpair.1 ⊆ Vsharp D P s.unpair.2) :=
    (dsharpPresentation P hD).incl_computable
  have hr : Nat.Primrec (fun s => Nat.pair (2 * s.unpair.1 + 2) s.unpair.2) :=
    (primrec_add₂ (primrec_mul₂ (Nat.Primrec.const 2) Nat.Primrec.left)
      (Nat.Primrec.const 2)).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun s => ?_) (hincl.comp hr)).re
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [pairSharp_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2]

end Proposition77
end DomainTheory.NeighbourhoodSystems
