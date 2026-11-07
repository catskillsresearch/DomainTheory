module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.iSupDirected

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Scott's Exercise 2.11: domains are closed under directed unions of ideal elements, and
approximable maps preserve those unions. -/
theorem exercise_2_11 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
      (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {Z : Set α},
      (iSupDirected a hdir).mem Z ↔ ∃ i, (a i).mem Z) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁) {I : Type*} [Nonempty I]
      (a : I → V₀.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k),
      f.toElementMap (iSupDirected a hdir) =
        iSupDirected (fun i => f.toElementMap (a i))
          (fun i j => by
            obtain ⟨k, hik, hjk⟩ := hdir i j
            exact ⟨k, f.toElementMap_mono hik, f.toElementMap_mono hjk⟩)) :=
  ⟨fun {_ _} {_ _} => mem_iSupDirected,
    fun {_ _} {_ _} => ApproximableMap.toElementMap_iSupDirected⟩

