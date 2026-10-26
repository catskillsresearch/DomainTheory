
module

public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_9
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_10
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE_erase
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_app
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_fresh_app
public import DomainTheory.DataTypesAsLattices.Functionality.finite_sigma_union_app
public import DomainTheory.DataTypesAsLattices.Functionality.finite_sigma_plain_app
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more


@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plotkin_function_related (p q : ℕ) :
    (arrowE
      (plotkinE p q (max p q + 1))
      (plotkinE p q (max p q + 1))).rel
        (graph (fun y => funOf (e p) y))
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1))) := by
  have hgf : graph (fun y => funOf (e p) y) =
      graph (fun y => funOf (graph (fun y => funOf (e p) y)) y) := by
    apply graph_ext
    intro y
    exact (beta (funOf.isScottContinuous (e p)) y).symm
  have hgu :
      graph (fun y => funOf (e p) y) ∪ graph (sigmaJ (max p q + 1)) =
        graph (fun y => funOf
          (graph (fun y => funOf (e p) y) ∪
            graph (sigmaJ (max p q + 1))) y) := by
    let F := fun y => funOf (e p) y ∪ sigmaJ (max p q + 1) y
    have hrep :
        graph (fun y => funOf (e p) y) ∪ graph (sigmaJ (max p q + 1)) =
          graph F := eq_2_10 _ _
    rw [hrep]
    congr 1
    funext y
    dsimp only [F]
    rw [← hrep]
    rw [eq_2_9, normalized_finite_app, sigmaJ.app]
  refine ⟨hgf, hgu, ?_⟩
  intro u v huv
  have herase := plotkinE_erase huv
  rcases huv.1 with ⟨r, hur | hur⟩
  <;> rcases huv.2.1 with ⟨s, hvs | hvs⟩
  all_goals
    subst u
    subst v
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      simpa [eraseTag.Z_finite] using herase
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y)) (Z r (e p) (e q)) =
          Z (r + 1) (e p) (e q) := by
      rw [normalized_finite_app]
      rfl
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q)) = Z (s + 1) (e p) (e q) :=
      finite_sigma_plain_app p q s
    rw [hleft, hright, ← hrs']
    exact ⟨⟨r + 1, Or.inl rfl⟩, ⟨r + 1, Or.inl rfl⟩,
      Relation.EqvGen.refl _⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      exact (eraseTag.Z_finite p q r).symm.trans
        (herase.trans (eraseTag.Z_finite_union p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y)) (Z r (e p) (e q)) =
          Z (r + 1) (e p) (e q) := by
      rw [normalized_finite_app]
      rfl
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q) ∪ {pair (max p q + 1) s}) =
          Z (s + 1) (e p) (e q) ∪
            {pair (max p q + 1) (s + 1)} :=
      finite_sigma_union_app p q s
    rw [hleft, hright, hrs']
    exact ⟨⟨s + 1, Or.inl rfl⟩, ⟨s + 1, Or.inr rfl⟩,
      Relation.EqvGen.rel _ _
        ⟨s + 1, Or.inl ⟨rfl, rfl⟩⟩⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      exact (eraseTag.Z_finite_union p q r).symm.trans
        (herase.trans (eraseTag.Z_finite p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y))
            (Z r (e p) (e q) ∪ {pair (max p q + 1) r}) =
          Z (r + 1) (e p) (e q) :=
      normalized_finite_fresh_app p q r
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q)) = Z (s + 1) (e p) (e q) :=
      finite_sigma_plain_app p q s
    rw [hleft, hright, ← hrs']
    exact ⟨⟨r + 1, Or.inl rfl⟩, ⟨r + 1, Or.inl rfl⟩,
      Relation.EqvGen.refl _⟩
  · have hrs : Z r (e p) (e q) = Z s (e p) (e q) := by
      simpa using (eraseTag.Z_finite_union p q r).symm.trans
        (herase.trans (eraseTag.Z_finite_union p q s))
    have hrs' : Z (r + 1) (e p) (e q) = Z (s + 1) (e p) (e q) := by
      simpa [Z] using congrArg (fun w => funOf (e p) w) hrs
    have hleft :
        funOf (graph (fun y => funOf (e p) y))
            (Z r (e p) (e q) ∪ {pair (max p q + 1) r}) =
          Z (r + 1) (e p) (e q) :=
      normalized_finite_fresh_app p q r
    have hright :
        funOf
            (graph (fun y => funOf (e p) y) ∪
              graph (sigmaJ (max p q + 1)))
            (Z s (e p) (e q) ∪ {pair (max p q + 1) s}) =
          Z (s + 1) (e p) (e q) ∪
            {pair (max p q + 1) (s + 1)} :=
      finite_sigma_union_app p q s
    rw [hleft, hright, hrs']
    exact ⟨⟨s + 1, Or.inl rfl⟩, ⟨s + 1, Or.inr rfl⟩,
      Relation.EqvGen.rel _ _
        ⟨s + 1, Or.inl ⟨rfl, rfl⟩⟩⟩

end DomainTheory.DataTypesAsLattices
