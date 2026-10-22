/-ai
For a computable presentation of a neighbourhood system D, the sharp injection is a computable map into the sharp presentation.

The relation on index codes must be recursively enumerable. Inclusion of sharp neighbourhoods is recursively decidable, and the map sending a code to the pair of one plus twice its first component with its second component is primitive recursive. After that reindexing, the injection relates the enumerated neighbourhoods exactly when the sharp neighbourhood at the resulting odd index is contained in the codomain neighbourhood, because an odd index is a zero-embedding and every enumerated set is a neighbourhood. The inclusion decider composed with the reindexing therefore decides the relation, and a decidable predicate is recursively enumerable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Proposition 7.7 (Scott 1981, PRG-19) — `λx. x^§` is computable.**
`Xₙ (λx.x^§) V_k ↔ V_{2n+1} ⊆ V_k` (`embZero Xₙ ⊆ V_k`), a recursive slice of the inclusion
decider for `D^§`, hence r.e. -/
theorem inSharp_isComputable (P : ComputablePresentation D) :
    ComputableMap P (dsharpPresentation P hD) (inSharpMap hD) := by
  constructor
  show REPred (fun s => (inSharpMap hD).rel (P.X s.unpair.1) (Vsharp D P s.unpair.2))
  have hincl : RecDecidable (fun s => Vsharp D P s.unpair.1 ⊆ Vsharp D P s.unpair.2) :=
    (dsharpPresentation P hD).incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (2 * t.unpair.1 + 1) t.unpair.2) :=
    (primrec_add₂ (primrec_mul₂ (Nat.Primrec.const 2) Nat.Primrec.left)
      (Nat.Primrec.const 1)).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [inSharpMap_rel, unpair_pair_fst, unpair_pair_snd, Vsharp_odd]
  exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, Vsharp_mem P _, h⟩⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
