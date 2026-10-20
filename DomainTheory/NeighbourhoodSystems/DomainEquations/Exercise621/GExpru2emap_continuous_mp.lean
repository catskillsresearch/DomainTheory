module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}










/-- Forward direction of continuity on maps for `GExpr`. -/
theorem GExpr.map_continuous_mp : (T : GExpr) → {I : Type} → {X Y : ScottSys} →
    {g : I → ApproximableMap X.sys Y.sys} → {f : ApproximableMap X.sys Y.sys} →
    [Nonempty I] → (∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k) →
    (∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) →
    {A B : Set Str} → (T.map f).rel A B → ∃ i, (T.map (g i)).rel A B
  | .const _, _, _, _, _, _, _, _, _, _, _, hrel => by
      obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, hrel⟩
  | .var, _, _, _, _, _, _, _, hf, A, B, hrel => (hf A B).mp hrel
  | .sum a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, rfl, rfl⟩ | ⟨Q, Q', hr, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := b.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, rfl, rfl⟩)⟩
  | .prod a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      obtain ⟨P, Q, P', Q', hr0, hr1, rfl, rfl⟩ := hrel
      obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr0
      obtain ⟨j, hj⟩ := b.map_continuous_mp hdir hf hr1
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, P, Q, P', Q', (a.map_mono hik) P P' hi, (b.map_mono hjk) Q Q' hj, rfl, rfl⟩
  | .oplus a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, hPne, hP'ne, rfl, rfl⟩ |
        ⟨Q, Q', hr, hQne, hQ'ne, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, hPne, hP'ne, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := b.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, hQne, hQ'ne, rfl, rfl⟩)⟩
  | .otimes a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, Q, P', Q', hr0, hr1, hPne, hQne, hP'ne, hQ'ne, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr0
        obtain ⟨j, hj⟩ := b.map_continuous_mp hdir hf hr1
        obtain ⟨k, hik, hjk⟩ := hdir i j
        exact ⟨k, Or.inr ⟨P, Q, P', Q', (a.map_mono hik) P P' hi, (b.map_mono hjk) Q Q' hj,
          hPne, hQne, hP'ne, hQ'ne, rfl, rfl⟩⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
