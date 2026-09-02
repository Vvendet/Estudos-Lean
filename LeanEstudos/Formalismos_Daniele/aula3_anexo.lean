import LeanEstudos.Formalismos_Daniele.aula2_anexo

-- Definições de Sistemas Completos
-----------------------------------------

/-- Um sistema é semi-completo se for fracamente normalizante e confluente.
    Isso garante que toda redução leva a uma forma normal única. -/
def ARSSemiComplete {α : Type} (R : ARS α) : Prop :=
  WeaklyNormalizing R ∧ IsConfluent R

/-- Um sistema é completo (ou convergente) se for fortemente normalizante e confluente. -/
def ARSComplete {α : Type} (R : ARS α) : Prop :=
  StronglyNormalizing R ∧ IsConfluent R

-- Lema de Newman
-----------------------------------------

lemma IsConfluent.locally_confluent {α : Type} {R : ARS α} (h : IsConfluent R) :
  LocallyConfluent R := by
  intro x y z hxy hxz
  have hreducesStarxy : ReducesStar R x y := by
    exact Reduces.toReducesStar hxy
  have hreducesStarxz : ReducesStar R x z := by
    exact Reduces.toReducesStar hxz
  have hjoinable : IsJoinable R y z := by
    exact h x y z hreducesStarxy hreducesStarxz
  exact hjoinable

/-- O Lema de Newman estabelece que, sob a hipótese de forte normalização,
    a confluência local é condição suficiente para a confluência global. -/
theorem Newmans_Lemma
    {α : Type} (R : ARS α)
    (hsn : StronglyNormalizing R) :
    IsConfluent R ↔ LocallyConfluent R:= by
    constructor
    · intro hconfluent
      exact IsConfluent.locally_confluent hconfluent
    · intro hlocally_confluent
      have hwfi : ARS.WFI R := (ARS.WFI_iff_StronglyNormalizing R).mpr hsn
      let P : α → Prop := fun x =>
        ∀ y z, ReducesStar R x y → ReducesStar R x z → ∃ w, ReducesStar R y w ∧ ReducesStar R z w
      have hind : ∀ x, (∀ x', Reduces R x x' → P x') → P x := by
        intro x ih y z hxy hxz
        have hxy_rtg := ReducesStar_iff_ReducesStar'.mp hxy
        have hxz_rtg := ReducesStar_iff_ReducesStar'.mp hxz
        have cases_y := Relation.ReflTransGen.cases_head hxy_rtg
        have cases_z := Relation.ReflTransGen.cases_head hxz_rtg
        rcases cases_y with (rfl | ⟨y1, hxy1, hy1y⟩)
        · exact ⟨z, hxz, ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl⟩
        rcases cases_z with (rfl | ⟨z1, hxz1, hz1z⟩)
        · exact ⟨y, ReducesStar_iff_ReducesStar'.mpr Relation.ReflTransGen.refl, hxy⟩
        · rcases hlocally_confluent x y1 z1 hxy1 hxz1 with ⟨u, hy1u, hz1u⟩
          have hy1y_star := ReducesStar_iff_ReducesStar'.mpr hy1y
          have hz1z_star := ReducesStar_iff_ReducesStar'.mpr hz1z
          have hP_y1 := ih y1 hxy1
          rcases hP_y1 y u hy1y_star hy1u with ⟨v, hyv, huv⟩
          have hz1v_star : ReducesStar R z1 v := ReducesStar.trans hz1u huv
          have hP_z1 := ih z1 hxz1
          rcases hP_z1 z v hz1z_star hz1v_star with ⟨w, hzw, hvw⟩
          have hyw : ReducesStar R y w := ReducesStar.trans hyv hvw
          exact ⟨w, hyw, hzw⟩
      intro x y z hxy hxz
      exact hwfi P hind x y z hxy hxz
