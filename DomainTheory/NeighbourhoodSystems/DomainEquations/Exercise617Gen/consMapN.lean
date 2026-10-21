/-ai
The successor consMapN a is the approximable endomap of Cn A that prepends the letter a. Its relation holds between neighbourhoods X and Y exactly when both are neighbourhoods of Cn and the set obtained by prepending a to the strings of X is contained in Y. The domain and codomain of a related pair are the first and second conjuncts. The master neighbourhood is related to itself because it is the cone of the empty string, which is the whole token set, and the inclusion of its prefixed copy is immediate. If two codomain neighbourhoods both contain the prefixed copy of X, so does their intersection; that prefixed copy is a neighbourhood, so the intersection law of Cn makes the intersection a neighbourhood. A smaller domain neighbourhood and a larger codomain neighbourhood remain related because prepending a preserves inclusions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_prependN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

/-- **The successor `x ↦ a·x`** prepending the letter `a`: `X (a·x) Y ↔ aX ⊆ Y`. -/
def consMapN (a : A) : ApproximableMap (Cn A) (Cn A) where
  rel X Y := memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Or.inl ⟨[], coneN_nil.symm⟩, Or.inl ⟨[], coneN_nil.symm⟩,
    fun _ _ => trivial⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    have hsubInter : prependN [a] X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hZ : memCn (prependN [a] X) := memCn_prependN [a] hX
    exact ⟨hX, (Cn A).inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prependN_mono [a] hX'X).trans (hXY.trans hYY')⟩

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
