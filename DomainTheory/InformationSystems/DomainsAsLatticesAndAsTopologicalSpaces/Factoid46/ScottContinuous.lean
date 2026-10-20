module


public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45

@[expose] public section

namespace DomainTheory.InformationSystems
namespace InfoSys

open DomainTheory.InformationSystems.Constructive

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Image of a nonempty set under a function is nonempty. -/
theorem nonempty_image {X Y : Type*} {S : Set X} (hne : S.Nonempty) (f : X → Y) :
    (f '' S).Nonempty :=
  hne.image f

/-- Monotone images preserve directedness. -/
theorem directed_image {A : InfoSys α} {B : InfoSys β} {S : Set A.Element}
    (hdir : A.IsDirected S) (f : A.Element → B.Element)
    (hmono : ∀ {x y}, x ≤ y → f x ≤ f y) : B.IsDirected (f '' S) := by
  intro x y hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨z₀, hz₀, hxz, hyz⟩ := hdir x₀ y₀ hx₀ hy₀
  exact ⟨f z₀, ⟨z₀, hz₀, rfl⟩, hmono hxz, hmono hyz⟩

/-- Scott-continuous map of domains: monotone and preserves directed lubs. -/
structure ScottContinuous (A : InfoSys α) (B : InfoSys β) where
  toFun : A.Element → B.Element
  mono' : ∀ {x y : A.Element}, x ≤ y → toFun x ≤ toFun y
  map_directedSup :
    ∀ (S : Set A.Element) (hne : S.Nonempty) (hdir : A.IsDirected S),
      toFun (A.directedSup S hne hdir) =
        B.directedSup (toFun '' S) (nonempty_image hne toFun)
          (directed_image hdir toFun mono')

end InfoSys
end DomainTheory.InformationSystems
