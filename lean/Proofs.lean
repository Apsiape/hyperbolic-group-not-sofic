import Statements
set_option maxRecDepth 100000

namespace PaperProofs

section
/-- Theorem 1.1 (v1.0). -/
theorem theorem_1_1 : PaperStatements.theorem_1_1 :=
  @Approx252.exists_torsionFree_wordHyperbolic_not_sofic
end

section
universe u_1
/-- Theorem 3.1 (thm:ineq). -/
theorem theorem_3_1 : PaperStatements.theorem_3_1.{u_1} :=
  @NonSofic.presentation_ineq.{u_1}
end

section
universe u_1
/-- Theorem 1.2, general constant. -/
theorem theorem_1_2_general : PaperStatements.theorem_1_2_general.{u_1} :=
  @NonSofic.presentation_quant.{u_1}
end

section
/-- Theorem 1.2, Lemma 2.2 data. -/
theorem theorem_1_2_lemma22 : PaperStatements.theorem_1_2_lemma22 :=
  @NonSofic.quant_lemma22
end

section
universe u
/-- Corollary 1.3, universal word. -/
theorem corollary_1_3_word : PaperStatements.corollary_1_3_word.{u} :=
  @NonSofic.exists_rect_word_killed_by_sofic_univ.{u}
end

section
universe u_1
/-- Corollary 1.3, quotient. -/
theorem corollary_1_3_quotient : PaperStatements.corollary_1_3_quotient.{u_1} :=
  @NonSofic.quotient_not_sofic.{u_1}
end

section
/-- Lemma 6.2. -/
theorem lemma_6_2 : PaperStatements.lemma_6_2 :=
  @NonSofic.LineFree.lineSubgroup_free
end

section
universe u_1
/-- Theorem 6.1. -/
theorem theorem_6_1 : PaperStatements.theorem_6_1.{u_1} :=
  @NonSofic.collapse.{u_1}
end

section
universe u_1
/-- Theorem 6.1, group ring. -/
theorem theorem_6_1_groupRing : PaperStatements.theorem_6_1_groupRing.{u_1} :=
  @NonSofic.collapse_groupRing.{u_1}
end

section
universe u_1 u_2 u_3
/-- Lemma 6.3. -/
theorem lemma_6_3 : PaperStatements.lemma_6_3.{u_1, u_2, u_3} :=
  @NonSofic.isUnit_map_of_zQuotientData.{u_1, u_2, u_3}
end

section
universe u_1 u_2 u_3
/-- Theorem 1.4. -/
theorem theorem_1_4 : PaperStatements.theorem_1_4.{u_1, u_2, u_3} :=
  @NonSofic.linnell.{u_1, u_2, u_3}
end

section
universe u_1 u_2 u_3 u_4
/-- Corollary 6.5, algebraic part. -/
theorem corollary_6_5_algebraic : PaperStatements.corollary_6_5_algebraic.{u_1, u_2, u_3, u_4} :=
  @NonSofic.not_isLinnell_of_split.{u_1, u_2, u_3, u_4}
end

section
universe u v w
/-- Combined data. -/
theorem headline_data : PaperStatements.headline_data.{u, v, w} :=
  @NonSofic.headline_data.{u, v, w}
end

section
universe u v w
/-- Combined statement. -/
theorem headline : PaperStatements.headline.{u, v, w} :=
  @NonSofic.headline.{u, v, w}
end

end PaperProofs
