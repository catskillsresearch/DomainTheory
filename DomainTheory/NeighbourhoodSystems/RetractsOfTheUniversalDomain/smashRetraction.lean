module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixOfO

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap ApproximableMap₂

/- concordance: source L4807 EXAMPLES 8.4 smash retraction -/

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- `(prod D E).bot = ⟨⊥_D, ⊥_E⟩`. -/
theorem pair_bot_bot : pair (D.bot) (E.bot) = (prod D E).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨D.master, E.master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

@[simp] theorem prod_bot_fst : ((prod D E).bot).fst = D.bot := by rw [← pair_bot_bot, fst_pair]

@[simp] theorem prod_bot_snd : ((prod D E).bot).snd = E.bot := by rw [← pair_bot_bot, snd_pair]

/-- The inner application `fade(check(y), z)` of Scott's `smash(x, y) = fade(check(x),
fade(check(y), ⟨x, y⟩))`: here `z = ⟨x, y⟩` is passed through `idMap` (Scott's `⟨x,y⟩` *is* the
ambient input). -/
def smashFadeInner : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))

/-- **Example 8.4(b)(ii)'s `smash` combinator.** `smash(x, y) = fade(check(x), fade(check(y),
⟨x, y⟩))`. -/
def smashRetraction : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) (smashFadeInner (D := D) (E := E)))

/-- **The compactness lemma.** If neither coordinate of `z` is `⊥`, some *proper* smash
neighbourhood witnesses `z.mem Y ⊆ Z` for any `Z ∈ z` — built from `exists_mem_ne_master_of_ne_bot`
witnesses on each coordinate, intersected against `Z`'s own decomposition via the *filter*
`inter_mem` of `z.fst`/`z.snd` (no `NeighborhoodSystem`-level consistency witness needed). -/
theorem exists_smash_witness {z : (prod D E).Element} (hx : z.fst ≠ D.bot) (hy : z.snd ≠ E.bot)
    {Z : Set (α ⊕ β)} (hzZ : z.mem Z) :
    ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  obtain ⟨X0, hX0, hX0ne⟩ := exists_mem_ne_master_of_ne_bot hx
  obtain ⟨Y0, hY0, hY0ne⟩ := exists_mem_ne_master_of_ne_bot hy
  set A := Sum.inl ⁻¹' Z with hA
  set B := Sum.inr ⁻¹' Z with hB
  have hZeq : Z = prodNbhd A B := prodNbhd_preimage (z.sub hzZ)
  have hAmem : D.mem A := prod_mem_inl (z.sub hzZ)
  have hBmem : E.mem B := prod_mem_inr (z.sub hzZ)
  rw [hZeq] at hzZ
  have hzfA : z.fst.mem A := mem_fst.mpr ⟨hAmem, ((prod_mem_split hAmem hBmem).mp hzZ).1⟩
  have hzsB : z.snd.mem B := mem_snd.mpr ⟨hBmem, ((prod_mem_split hAmem hBmem).mp hzZ).2⟩
  have hzfX0' : z.fst.mem (X0 ∩ A) := z.fst.inter_mem hX0 hzfA
  have hzsY0' : z.snd.mem (Y0 ∩ B) := z.snd.inter_mem hY0 hzsB
  have hX0'mem : D.mem (X0 ∩ A) := z.fst.sub hzfX0'
  have hY0'mem : E.mem (Y0 ∩ B) := z.snd.sub hzsY0'
  have hX0'ne : X0 ∩ A ≠ D.master := Exercise510.inter_ne_master_left (z.fst.sub hX0) hX0ne
  have hY0'ne : Y0 ∩ B ≠ E.master := Exercise510.inter_ne_master_right (z.snd.sub hY0) hY0ne
  refine ⟨prodNbhd (X0 ∩ A) (Y0 ∩ B),
    Exercise510.smash_mem_proper hX0'mem hX0'ne hY0'mem hY0'ne, ?_, ?_⟩
  · exact (prod_mem_split hX0'mem hY0'mem).mpr
      ⟨(mem_fst.mp hzfX0').2, (mem_snd.mp hzsY0').2⟩
  · rw [hZeq]
    exact prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩

theorem smashFadeInner_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashFadeInner.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧ (Z = (prod D E).master ∨ (z.snd ≠ E.bot ∧ z.mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁,
    toElementMap_idMap, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

theorem smashRetraction_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ (smashFadeInner.toElementMap z).mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) smashFadeInner)).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

/-- **`smashRetraction`'s closed form.** `smash(z) = z` if neither coordinate is `⊥`; otherwise
`smash(z) = ⊥`. -/
theorem smashRetraction_mem_iff {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ z.snd ≠ E.bot ∧ z.mem Z)) := by
  rw [smashRetraction_mem, smashFadeInner_mem]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨hx, hPZ', hZeq' | ⟨hy, hzZ⟩⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inl hZeq'⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hy, hzZ⟩⟩
  · rintro ⟨hPZ, hZeq | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hPZ, Or.inr ⟨hy, hzZ⟩⟩⟩

theorem smashRetraction_le_idMap : smashRetraction (D := D) (E := E) ≤ idMap (prod D E) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_idMap]
  intro Z hZ
  rw [smashRetraction_mem_iff] at hZ
  rcases hZ with ⟨hPZ, rfl | ⟨-, -, hzZ⟩⟩
  · exact z.master_mem
  · exact hzZ

theorem smashRetraction_of_eq_bot {z : (prod D E).Element} (hz : z.fst = D.bot ∨ z.snd = E.bot) :
    smashRetraction.toElementMap z = (prod D E).bot := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hx, hy, -⟩⟩
    · rfl
    · exact absurd hz (by simp [hx, hy])
  · rintro rfl
    exact ⟨(prod D E).master_mem, Or.inl rfl⟩

theorem smashRetraction_of_ne_bot {z : (prod D E).Element} (hx : z.fst ≠ D.bot)
    (hy : z.snd ≠ E.bot) : smashRetraction.toElementMap z = z := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨-, -, hzZ⟩⟩
    · rw [hZeq]; exact z.master_mem
    · exact hzZ
  · intro hzZ
    exact ⟨z.sub hzZ, Or.inr ⟨hx, hy, hzZ⟩⟩

theorem isRetraction_smashRetraction : Retraction (smashRetraction (D := D) (E := E)) := by
  constructor
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_comp]
  by_cases hx : z.fst = D.bot
  · rw [smashRetraction_of_eq_bot (Or.inl hx),
      smashRetraction_of_eq_bot (Or.inl prod_bot_fst)]
  · by_cases hy : z.snd = E.bot
    · rw [smashRetraction_of_eq_bot (Or.inr hy),
        smashRetraction_of_eq_bot (Or.inr prod_bot_snd)]
    · rw [smashRetraction_of_ne_bot hx hy, smashRetraction_of_ne_bot hx hy]

/-- **The subsystem relation `Exercise510.smash D E ◁ prod D E`.** Every smash neighbourhood is a
product neighbourhood; a proper smash neighbourhood stays proper (hence smash-membership, not just
product-membership) after any consistent intersection, by `Exercise510.inter_ne_master_left/right`
exactly as in `Exercise510.smash`'s own closure proof. -/
theorem smash_subsystem_prod : Exercise510.smash D E ◁ prod D E where
  master_eq := by rw [Exercise510.smash_master, prod_master]
  sub := by
    rintro W (rfl | ⟨X, Y, hX, -, hY, -, rfl⟩)
    · exact prod_mem_prodNbhd D.master_mem E.master_mem
    · exact prod_mem_prodNbhd hX hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hPint
    · -- `W = smash master = prod master`.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (D.sub_master hX'),
          Set.inter_eq_right.mpr (E.sub_master hY')]
    · -- `W = prodNbhd X Y` proper.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (D.sub_master hX),
          Set.inter_eq_left.mpr (E.sub_master hY)]
      · -- both proper: `hPint` supplies the membership of the intersection in `prod D E`.
        rw [prodNbhd_inter] at hPint ⊢
        obtain ⟨hXX'mem, hYY'mem⟩ := prod_mem_prodNbhd_iff.mp hPint
        exact Or.inr ⟨X ∩ X', Y ∩ Y', hXX'mem, Exercise510.inter_ne_master_left hX hXne, hYY'mem,
          Exercise510.inter_ne_master_right hY hYne, rfl⟩

/-- The closed form of `Subsystem.retractionOfSubsystem`'s elementwise action, specialized to
`smash_subsystem_prod`, simplified using that `z` is already up-closed: the existential witness
`X ⊆ Y ⊆ Z` of Proposition 8.2's formula collapses to `z.mem Y` directly. -/
theorem mem_toElementMap_retractionOfSubsystem_smash {z : (prod D E).Element}
    {Z : Set (α ⊕ β)} :
    ((Subsystem.retractionOfSubsystem (smash_subsystem_prod (D := D) (E := E))).toElementMap z).mem
        Z ↔
      (prod D E).mem Z ∧ ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hzX, hrel⟩
    obtain ⟨hPX, hPZ, Y, hSY, hXY, hYZ⟩ := (Subsystem.retractionOfSubsystem_rel _).mp hrel
    exact ⟨hPZ, Y, hSY, z.up_mem hzX (smash_subsystem_prod.sub hSY) hXY, hYZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    exact ⟨Y, hzY, (Subsystem.retractionOfSubsystem_rel _).mpr
      ⟨z.sub hzY, hPZ, Y, hSY, subset_rfl, hYZ⟩⟩

/-- **Scott's `smash` combinator equals Proposition 8.2's canonical subsystem retraction.** Both
sides agree with `smashRetraction_mem_iff`'s closed form: the `Z = master` branch matches (both
sides always admit the master witness `Y = (smash D E).master`), and the "genuine pair" branch
matches by `exists_smash_witness` (`←`) and a direct case split on `(smash D E).mem Y` (`→`, using
that `Y ⊆ (prod D E).master` sandwiches `Z = master` when `Y` is itself the master, and that
`z.fst.mem`/`z.snd.mem` of a proper `Y`'s factors forces both coordinates non-`⊥`, `mem_bot`). -/
theorem smashRetraction_eq_retractionOfSubsystem :
    smashRetraction (D := D) (E := E) = Subsystem.retractionOfSubsystem smash_subsystem_prod := by
  apply ext_of_toElementMap
  intro z
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_toElementMap_retractionOfSubsystem_smash]
  constructor
  · rintro ⟨hPZ, rfl | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, (prod D E).master, Exercise510.smash_mem_iff.mpr (Or.inl rfl), z.master_mem,
        subset_rfl⟩
    · exact ⟨hPZ, exists_smash_witness hx hy hzZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    rcases Exercise510.smash_mem_iff.mp hSY with rfl | ⟨YA, YB, hYA, hYAne, hYB, hYBne, rfl⟩
    · exact ⟨hPZ, Or.inl (Set.Subset.antisymm ((prod D E).sub_master hPZ) hYZ)⟩
    · have hzfYA : z.fst.mem YA := mem_fst.mpr ⟨hYA, ((prod_mem_split hYA hYB).mp hzY).1⟩
      have hzsYB : z.snd.mem YB := mem_snd.mpr ⟨hYB, ((prod_mem_split hYA hYB).mp hzY).2⟩
      refine ⟨hPZ, Or.inr ⟨?_, ?_, z.up_mem hzY hPZ hYZ⟩⟩
      · intro hxbot; rw [hxbot, mem_bot] at hzfYA; exact hYAne hzfYA
      · intro hybot; rw [hybot, mem_bot] at hzsYB; exact hYBne hzsYB

/-- **Example 8.4(b)(ii) (Scott 1981, PRG-19).** `smashRetraction` is a projection on `D × E`
whose fixed-point set is isomorphic to the smash product `Exercise510.smash D E`. -/
theorem example84b_smash :
    IsProjection (smashRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.smash D E).Element ≃o
        {z : (prod D E).Element // smashRetraction.toElementMap z = z}) := by
  rw [smashRetraction_eq_retractionOfSubsystem]
  exact ⟨Subsystem.isProjection_retractionOfSubsystem smash_subsystem_prod,
    ⟨Subsystem.elementIso smash_subsystem_prod⟩⟩
end

end DomainTheory.NeighbourhoodSystems
