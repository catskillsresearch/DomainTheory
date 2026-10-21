/-ai
In the forward direction of continuity on domains, a neighbourhood of T(U) already belongs to T(D) for some D in the directed nonempty family.

The proof is by induction on T. A constant keeps the membership and uses any member of the nonempty family. The variable is the given characterization of membership in U. For a separated sum, the master uses any family member, because the subsystem master equality identifies the masters, and a left or right tag uses the inductive hypothesis on that component. For a separated product, the two coordinates give two family members, directedness supplies a common upper bound, and the subsystem relation transports both memberships. For a coalesced sum, the master is as in the separated sum, and a proper tag uses the corresponding inductive hypothesis; properness survives because equality with the master at that member would become equality with the master at U after the subsystem master equality. For a smash product, the master is as before, and a proper rectangle uses both inductive hypotheses and a common upper bound, with properness preserved by the same master equality at that upper bound.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_subsystem

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









/-- Forward direction of continuity on domains for `GExpr`. -/
theorem GExpr.obj_continuous_mp : (T : GExpr) → {ℱ : Set ScottSys} → {U : ScottSys} →
    DirectedOn (fun a b => a.sys ◁ b.sys) ℱ → ℱ.Nonempty →
    (∀ D ∈ ℱ, D.sys ◁ U.sys) → (∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X) →
    {W : Set Str} → (T.obj U).sys.mem W → ∃ D ∈ ℱ, (T.obj D).sys.mem W
  | .const _, _, _, _, hne, _, _, _, hmem => by
      obtain ⟨D, hD⟩ := hne; exact ⟨D, hD, hmem⟩
  | .var, _, _, _, _, _, hU, W, hmem => (hU W).mp hmem
  | .sum a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.sum a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        exact ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, rfl⟩)⟩
      · obtain ⟨D, hD, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        exact ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, rfl⟩)⟩
  | .prod a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      obtain ⟨X, Y, hX, hY, rfl⟩ := hmem
      obtain ⟨D₁, hD₁, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
      obtain ⟨D₂, hD₂, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
      obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
      exact ⟨D₃, hD₃, X, Y, (a.obj_subsystem hr1).sub hXD, (b.obj_subsystem hr2).sub hYD, rfl⟩
  | .oplus a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.oplus a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        refine ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, ?_, rfl⟩)⟩
        exact fun heq => hXne (heq.trans (a.obj_subsystem (hsub D hD)).master_eq)
      · obtain ⟨D, hD, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        refine ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, ?_, rfl⟩)⟩
        exact fun heq => hYne (heq.trans (b.obj_subsystem (hsub D hD)).master_eq)
  | .otimes a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.otimes a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D₁, hD₁, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        obtain ⟨D₂, hD₂, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
        refine ⟨D₃, hD₃, Or.inr ⟨X, Y, (a.obj_subsystem hr1).sub hXD,
          (b.obj_subsystem hr2).sub hYD, ?_, ?_, rfl⟩⟩
        · exact fun heq => hXne (heq.trans (a.obj_subsystem (hsub D₃ hD₃)).master_eq)
        · exact fun heq => hYne (heq.trans (b.obj_subsystem (hsub D₃ hD₃)).master_eq)

end Exercise619
end DomainTheory.NeighbourhoodSystems
