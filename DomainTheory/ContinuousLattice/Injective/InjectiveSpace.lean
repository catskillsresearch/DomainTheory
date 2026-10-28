module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

open Topology TopologicalSpace

universe u v w

class InjectiveSpace (D : Type v) [TopologicalSpace D] : Prop where
  extension :
    ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
      IsEmbedding e → ∀ f : C(X, D), ∃ g : C(Y, D), ∀ x, g (e x) = f x

abbrev Sierpinski := Prop

namespace InjectiveSpace

theorem sierpinski : InjectiveSpace.{u} Sierpinski := by
  constructor
  intro X Y _ _ e he f
  have hfopen : IsOpen {x | f x} := continuous_Prop.1 f.continuous
  rw [he.isInducing.isOpen_iff] at hfopen
  obtain ⟨V, hVopen, hVeq⟩ := hfopen
  refine ⟨⟨fun y => y ∈ V, continuous_Prop.2 hVopen⟩, fun x => ?_⟩
  have : (e x ∈ V) = (x ∈ {x | f x}) := by rw [← hVeq]; rfl
  simpa using this

theorem pi {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, InjectiveSpace.{u} (D i)) : InjectiveSpace.{u} (∀ i, D i) := by
  constructor
  intro X Y _ _ e he f
  choose g hg using fun i =>
    (h i).extension e he ⟨fun x => f x i, (continuous_apply i).comp f.continuous⟩
  refine ⟨⟨fun y i => g i y, continuous_pi fun i => (g i).continuous⟩, fun x => ?_⟩
  funext i
  exact hg i x

theorem of_retract {D : Type v} {D' : Type v}
    [TopologicalSpace D] [TopologicalSpace D'] (hD : InjectiveSpace.{u} D)
    (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    InjectiveSpace.{u} D' := by
  constructor
  intro X Y _ _ e he f
  obtain ⟨g, hg⟩ := hD.extension e he (s.comp f)
  refine ⟨r.comp g, fun x => ?_⟩
  show r (g (e x)) = f x
  rw [hg x]
  exact hrs (f x)

end InjectiveSpace
