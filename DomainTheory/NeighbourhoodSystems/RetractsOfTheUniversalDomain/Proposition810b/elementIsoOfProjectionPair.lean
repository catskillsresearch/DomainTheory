module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Generalized Proposition 8.2 `elementIso`.** Given an approximable projection pair
`i : D → E`, `j : E → D` with `j ∘ i = I_D` (no requirement `i ∘ j ≤ I_E`, and `D`, `E` need not
share a token type — unlike `Subsystem.elementIso`, which requires a literal `D ◁ E`), and
`g : E → E` with `g = i ∘ j`, then `D.Element ≃o Fix(g)`. The proof is verbatim
`Subsystem.elementIso`'s, generalized. -/
def elementIsoOfProjectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    D.Element ≃o {y : E.Element // g.toElementMap y = y} where
  toFun x := ⟨i.toElementMap x, by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    rw [hg, toElementMap_comp, h1, hji, toElementMap_idMap]⟩
  invFun y := j.toElementMap y.1
  left_inv x := by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    show j.toElementMap (i.toElementMap x) = x
    rw [h1, hji, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : g.toElementMap y.1 = y.1 := y.2
    show i.toElementMap (j.toElementMap y.1) = y.1
    rw [← toElementMap_comp, ← hg]
    exact hfix
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := j.toElementMap_mono hle
      have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
        (toElementMap_comp j i x).symm
      have h2 : j.toElementMap (i.toElementMap x') = (j.comp i).toElementMap x' :=
        (toElementMap_comp j i x').symm
      rw [h1, h2, hji, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact i.toElementMap_mono hle

end DomainTheory.NeighbourhoodSystems
