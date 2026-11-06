module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.inducedMaps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.19 (iii)–(iv): projections recover the summands after sum-map. -/
theorem example_319_sum :
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
      (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁'),
      (outMap₀ (h₀ := h₀') (h₁ := h₁')).comp
        ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
          (inMap₀ (h₀ := h₀) (h₁ := h₁))) = f) ∧
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
      (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁'),
      (outMap₁ (h₀ := h₀') (h₁ := h₁')).comp
        ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
          (inMap₁ (h₀ := h₀) (h₁ := h₁))) = g) :=
  ⟨@outMap₀_comp_sumMap_comp_inMap₀, @outMap₁_comp_sumMap_comp_inMap₁⟩

/-- Scott's Exercise 3.19 (i)–(ii): product of maps acts componentwise. -/
theorem example_319 :
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
      (x : V₀.Element) (y : V₁.Element),
      (prodMap f g).toElementMap (pair x y) = pair (f.toElementMap x) (g.toElementMap y)) ∧
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') (w : (prod V₀ V₁).Element),
      (prodMap f g).toElementMap w =
        pair (f.toElementMap w.fst) (g.toElementMap w.snd)) :=
  ⟨@toElementMap_prodMap_pair, @toElementMap_prodMap⟩

end DomainTheory.NeighbourhoodSystems
