section \<open> Reactive Design Specifications \<close>

theory utp_rdes_designs
  imports utp_rdes_healths
begin

subsection \<open> Reactive design forms \<close>

lemma rdes_skip_def: "II\<^sub>C = \<^bold>R(true \<turnstile> ((tr\<^sup>< = tr\<^sup>>)\<^sub>e \<and> \<not> wait\<^sup>> \<and> \<lceil>II\<rceil>\<^sub>R))"
  apply pred_auto using minus_zero_eq by blast+

lemma srdes_skip_def: "II\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> ((tr\<^sup>> = tr\<^sup><)\<^sub>e \<and> \<not> wait\<^sup>> \<and> \<lceil>II\<rceil>\<^sub>R))"
  apply pred_auto using minus_zero_eq by blast+

(*
lemma Chaos_def: "Chaos = \<^bold>R\<^sub>s(false \<turnstile> true)"
proof -
  have "Chaos = SRD(true)"
    by (metis srdes_theory.healthy_bottom)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(true))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by (metis H1_design H2_true design_false_pre)
  finally show ?thesis .
qed

lemma Miracle_def: "Miracle = \<^bold>R\<^sub>s(true \<turnstile> false)"
proof -
  have "Miracle = SRD(false)"
    by (metis srdes_theory.healthy_top)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(false))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (metis (no_types, lifting) H1_H2_eq_design p_imp_p subst_impl subst_not utp_pred_laws.compl_bot_eq utp_pred_laws.compl_top_eq)
  finally show ?thesis .
qed
*)

lemma RD1_reactive_design: "RD1(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by pred_auto

lemma RD2_reactive_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "RD2(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RH_commute RD2_def)

lemma RD1_st_reactive_design: "RD1(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by pred_auto

lemma RD2_st_reactive_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "RD2(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RHS_commute RD2_def)

lemma wait_false_design:
  "(P \<turnstile> Q) \<^sub>f = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by pred_auto

lemma RD_RH_design_form:
  "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "RD(P) = RD1(RD2(R1(R2c(R3c(P)))))"
    by (simp add: RD_alt_def RH_def)
  also have "... = RD1(H2(R1(R2s(R3c(P)))))"
    by (simp add: R1_R2s_R2c RD2_def)
  also have "... = RD1(R1(H2(R2s(R3c(P)))))"
    by (simp add: R1_H2_commute)
  also have "... = R1(H1(R1(H2(R2s(R3c(P))))))"
    by (simp add: R1_idem RD1_via_R1)
  also have "... = R1(H1(H2(R2s(R3c(R1(P))))))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R2s_R2c R1_R3c_commute RD1_via_R1)
  also have "... = R1(R2s(H1(H2(R3c(R1(P))))))"
    by (simp add: R2s_H1_commute R2s_H2_commute)
  also have "... = R1(R2s(H1(R3c(H2(R1(P))))))"
    by (metis RD2_R3c_commute RD2_def)
  also have "... = R2(R1(H1(R3c(H2(R1(P))))))"
    by (metis R1_R2_commute R1_idem R2_def)
  also have "... = R2(R3c(R1(\<^bold>H(R1(P)))))"
    by (simp add: R1_R3c_commute RD1_R3c_commute RD1_via_R1)
  also have "... = RH(\<^bold>H(R1(P)))"
    by (metis R1_R2s_R2c R1_R3c_commute R2_R1_form RH_def)
  also have "... = RH(\<^bold>H(P))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R3c_commute R1_idem RD1_via_R1 RH_def)
  also have "... = RH((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by pred_auto
  finally show ?thesis .
qed

lemma RD_reactive_design:
  assumes "P is RD"
  shows "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis RD_RH_design_form Healthy_def' assms)

lemma RD_RH_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "RD(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (simp add: RD1_reactive_design RD2_reactive_design RD_alt_def RH_idem assms(1) assms(2))

lemma RH_design_is_RD:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "\<^bold>R(P \<turnstile> Q) is RD"
  by (simp add: RD_RH_design Healthy_def' assms(1) assms(2))

lemma SRD_RH_design_form:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "SRD(P) = R1(R2c(R3h(RD1(RD2(R1(P))))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_commute R1_R3h_commute R1_idem R2c_H2_commute RD1_R1_commute RD1_R2c_commute RD1_R3h_commute RD2_R3h_commute RD2_def RHS_def SRD_def)
  also have "... = R1(R2s(R3h(\<^bold>H(P))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_is_R2 R1_R3h_commute R2_R1_form RD1_via_R1 RD2_def)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(P))"
    by (simp add: R1_R2s_R2c RHS_def)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by pred_auto
  finally show ?thesis .
qed

lemma SRD_reactive_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis SRD_RH_design_form Healthy_def' assms)

lemma SRD_RH_design:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "SRD(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (simp add: RD1_st_reactive_design RD2_st_reactive_design RHS_idem SRD_def assms(1) assms(2))

lemma RHS_design_is_SRD:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q) is SRD"
  by (simp add: Healthy_def' SRD_RH_design assms(1) assms(2))

subsection \<open> Auxiliary healthiness conditions \<close>

definition [pred]: "R3c_pre(P) = (true \<triangleleft> wait\<^sup>< \<triangleright> P)"

expr_constructor R3c_pre

definition [pred]: "R3c_post(P) = (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> P)"

expr_constructor R3c_post

definition [pred]: "R3h_post(P) = ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>s/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> P)"

expr_constructor R3h_post

lemma R3c_pre_conj: "R3c_pre(P \<and> Q) = (R3c_pre(P) \<and> R3c_pre(Q))"
  by pred_auto

lemma R3c_pre_seq:
  "(true ;; Q) = true \<Longrightarrow> R3c_pre(P ;; Q) = (R3c_pre(P) ;; Q)"
  by pred_auto

lemma unrest_ok_R3c_pre [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R3c_pre(P)"
  by pred_auto
  
(* TODO: find missing lemma to prove this by unrest
 * by (simp add: R3c_pre_def cond_not_and unrest) *)

lemma unrest_ok'_R3c_pre [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def rcond_def unrest)

lemma unrest_ok_R3c_post [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R3c_post(P)"
  by pred_auto

lemma unrest_ok_R3c_post' [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def rcond_def unrest)

lemma unrest_ok_R3h_post [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R3h_post(P)"
  by pred_auto

lemma unrest_ok_R3h_post' [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R3h_post(P)"
  by pred_auto

subsection \<open> Composition laws \<close>

theorem R1_design_composition:
  fixes P Q :: "('t::trace,'\<alpha>,'\<beta>) rel_rp"
  and R S :: "('t,'\<beta>,'\<gamma>) rel_rp"
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) =
   R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
proof -
  have "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = ((R1 (P \<turnstile> Q))\<^sup>t ;; R1 (R \<turnstile> S)\<lbrakk>True/ok\<^sup><\<rbrakk> \<or> (R1 (P \<turnstile> Q))\<^sup>f ;; R1 (R \<turnstile> S)\<lbrakk>False/ok\<^sup><\<rbrakk>)"
    by (rule seqr_bool_split[of ok], simp)
  also from assms have "... = ((R1((ok\<^sup>< \<and> P) \<longrightarrow> (true \<and> Q)) ;; R1((true \<and> R) \<longrightarrow> (ok\<^sup>> \<and> S)))
                             \<or> (R1((ok\<^sup>< \<and> P) \<longrightarrow> (false \<and> Q)) ;; R1((false \<and> R) \<longrightarrow> (ok\<^sup>> \<and> S))))"
    apply (simp add: design_def R1_def)
    apply(pred_simp)
    (* TODO: why is unrest no longer able to handle this? *)
    apply(safe)
    apply(meson+)
    done
  also from assms have "... = ((R1((ok\<^sup>< \<and> P) \<longrightarrow> Q) ;; R1(R \<longrightarrow> (ok\<^sup>> \<and> S)))
                             \<or> (R1(\<not> (ok\<^sup>< \<and> P)) ;; R1(true)))"
    by simp
  also from assms have "... = ((R1(\<not> ok\<^sup>< \<or> \<not> P \<or> Q) ;; R1(\<not> R \<or> (ok\<^sup>> \<and> S)))
                             \<or> (R1(\<not> ok\<^sup>< \<or> \<not> P) ;; R1(true)))"
    by (simp add: impl_neg_disj pred_ba.sup_assoc)
  also from assms have "... = (((R1(\<not> ok\<^sup>< \<or> \<not> P) \<or> R1(Q)) ;; R1(\<not> R \<or> (ok\<^sup>> \<and> S)))
                               \<or> (R1(\<not> ok\<^sup>< \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj pred_ba.sup.assoc)
  also from assms have "... = ((R1(\<not> ok\<^sup>< \<or> \<not> P) ;; R1(\<not> R \<or> (ok\<^sup>> \<and> S)))
                               \<or> (R1(Q) ;; R1(\<not> R \<or> (ok\<^sup>> \<and> S)))
                               \<or> (R1(\<not> ok\<^sup>< \<or> \<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distl pred_ba.sup.assoc)
  also from assms have "... = ((R1(Q) ;; R1(\<not> R \<or> (ok\<^sup>> \<and> S)))
                               \<or> (R1(\<not> ok\<^sup>< \<or> \<not> P) ;; R1(true)))"
    by (pred_simp; blast)
  also from assms have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> ok\<^sup>>))
                               \<or> (R1(\<not> ok\<^sup>< \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_extend_conj pred_ba.inf.commute)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> ok\<^sup>>))
                  \<or> ((R1(\<not> ok\<^sup><) :: ('t,'\<alpha>,'\<beta>) rel_rp) ;; R1(true))
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj seqr_or_distl)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> ok\<^sup>>))
                  \<or> (R1(\<not> ok\<^sup><))
                  \<or> (R1(\<not> P) ;; R1(true)))"
  proof -
    have "((R1(\<not> ok\<^sup><) :: ('t,'\<alpha>,'\<beta>) rel_rp) ;; R1(true)) =
           (R1(\<not> ok\<^sup><) :: ('t,'\<alpha>,'\<gamma>) rel_rp)"
      by pred_auto
    thus ?thesis
      by simp
  qed
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> (R1(S \<and> ok\<^sup>>))))
                  \<or> R1(\<not> ok\<^sup><)
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_extend_conj)
  also have "... = ( (R1(Q) ;; (R1 (\<not> R)))
                   \<or> (R1(Q) ;; (R1(S \<and> ok\<^sup>>)))
                   \<or> R1(\<not> ok\<^sup><)
                   \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distr pred_ba.sup.assoc)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> (R1(Q) ;; (R1(S \<and> ok\<^sup>>)))
                     \<or> (\<not> ok\<^sup><)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_seqr)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> ((R1(Q) ;; R1(S)) \<and> ok\<^sup>>)
                     \<or> (\<not> ok\<^sup><)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (pred_auto; blast)
  also have "... = R1(\<not>(ok\<^sup>< \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                     \<or>  ((R1(Q) ;; R1(S)) \<and> ok\<^sup>>))"
    by (pred_simp; blast)
  also have "... = R1((ok\<^sup>< \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                      \<longrightarrow> (ok\<^sup>> \<and> (R1(Q) ;; R1(S))))"
    by (simp add: impl_neg_disj pred_ba.inf.commute)
  also have "... = R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
    by pred_auto
  finally show ?thesis .
qed

(* TODO: Waiting on reactive wp *)
(*
theorem R1_design_composition_RR:
  assumes "P is RR" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  apply (subst R1_design_composition)
  apply (simp_all add: assms unrest wp_rea_def Healthy_if closure)
  apply (rel_auto)
done

theorem R1_design_composition_RC:
  assumes "P is RC" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1((P \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  by (simp add: R1_design_composition_RR assms unrest Healthy_if closure wp)
*)

lemma R2s_design: "R2s(P \<turnstile> Q) = (R2s(P) \<turnstile> R2s(Q))"
  by (simp add: R2s_def design_def usubst)

lemma R2c_design: "R2c(P \<turnstile> Q) = (R2c(P) \<turnstile> R2c(Q))"
  by pred_auto
lemma R1_R3c_design:
  "R1(R3c(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by pred_auto

lemma R1_R3h_design:
  "R1(R3h(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3h_post(Q))"
  by pred_auto

lemma R3c_R1_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R3c(R1(P \<turnstile> Q)) ;; R3c(R1(R \<turnstile> S))) =
       R3c(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> wait\<^sup>>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
    by (pred_auto; blast)
  have 2:"(\<not> (R1 (R3c_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R)))"
    apply (pred_auto)
    apply blast
    apply (metis (full_types))
    apply blast
    done
  have 3:"(R1 (R3c_post Q) ;; R1 (R3c_post S)) = R3c_post (R1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1 S))"
    by (pred_auto; blast)
  show ?thesis
    apply (simp add: R3c_semir_form R1_R3c_commute[THEN sym] R1_R3c_design unrest )
    apply (subst R1_design_composition)
        apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
    done
qed

lemma R3h_R1_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R3h(R1(P \<turnstile> Q)) ;; R3h(R1(R \<turnstile> S))) =
       R3h(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> wait\<^sup>>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
   by (pred_auto; blast)
  have 2:"(\<not> (R1 (R3h_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R)))"
    apply (pred_auto)
    apply blast
    apply (metis (full_types))
    apply blast
    done
  have 3:"(R1 (R3h_post Q) ;; R1 (R3h_post S)) = R3h_post (R1 Q ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 S))"
    apply (pred_auto)
               apply blast
                apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    (* TODO: fix proof *)
    sorry
    
  show ?thesis
    apply (simp add: R3h_semir_form R1_R3h_commute[THEN sym] R1_R3h_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R2_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R2(P \<turnstile> Q) ;; R2(R \<turnstile> S)) =
       R2((\<not> (R1 (\<not> R2c P) ;; R1 true) \<and> \<not> (R1 (R2c Q) ;; R1 (\<not> R2c R))) \<turnstile> (R1 (R2c Q) ;; R1 (R2c S)))"
  apply (simp add: R2_R2c_def R2c_design R1_design_composition assms unrest R2c_not R2c_and R2c_disj R1_R2c_commute[THEN sym] R2c_idem R2c_R1_seq)
  apply (metis (no_types, lifting) R2c_R1_seq R2c_not R2c_true)
done

lemma RH_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(RH(P \<turnstile> Q) ;; RH(R \<turnstile> S)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> wait\<^sup>>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by pred_auto
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> wait\<^sup>>) ;; R2 (\<not> R))"
      by pred_auto
    hence "R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> wait\<^sup>>) ;; R2 (\<not> R))"
      by (metis (mono_tags, lifting) R1_R2c_commute R1_R2s_R2c R2_def R2_seqr_distribute)    
    also have "... = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
      by pred_auto
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S)))) = (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S)))"
    apply pred_auto
    apply (metis diff_add_cancel_left' le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
    by (metis diff_add_cancel_left' minus_cancel_le)

  have "(R1(R2s(R3c(P \<turnstile> Q))) ;; R1(R2s(R3c(R \<turnstile> S)))) =
        ((R3c(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3c(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c R1_R3c_commute R2c_R3c_commute R2s_design)
  also have "... = R3c (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S)))))"
    by (simp add: R3c_R1_design_composition assms unrest)
  also have "... = R3c(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3c_commute R2c_R3c_commute RH_def)
qed

lemma cond_unit_T:"(P \<triangleleft> True \<triangleright> Q) = P"
  by (pred_auto)

lemma RHS_design_composition:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> wait\<^sup>>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (pred_auto, blast)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> wait\<^sup>>) ;; R2 (\<not> R))"
      by (pred_auto, blast+)
    hence "R2c ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> wait\<^sup>>) ;; R2 (\<not> R))"
      by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))"
      by (pred_auto, blast+)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S)))) =
          (R1 (R2s Q) ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S)))"
  (* Sledgehammer apply proof *)
    apply pred_auto
    apply (metis diff_add_cancel_left' le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
    apply blast
    apply blast
    apply (metis diff_add_cancel_left' minus_cancel_le)
    apply blast
    by blast

  have "(R1(R2s(R3h(P \<turnstile> Q))) ;; R1(R2s(R3h(R \<turnstile> S)))) =
        ((R3h(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3h(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c R1_R3h_commute R2c_R3h_commute R2s_design)
  also have "... = R3h (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S)))))"
    by (simp add: R3h_R1_design_composition assms unrest)
  also have "... = R3h(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; ((\<Sqinter>s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3h_commute R2c_R3h_commute RHS_def)
qed

lemma RHS_R2s_design_composition:
  assumes
    "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    "P is R2s" "Q is R2s" "R is R2s" "S is R2s"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> P) ;; R1 true) \<and> \<not> ((R1 Q \<and> \<not> wait\<^sup>>) ;; R1 (\<not> R))) \<turnstile>
                       (R1 Q ;; ((\<Sqinter> s. \<lceil>II\<rceil>\<^sub>D\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup><\<rbrakk>) \<triangleleft> wait\<^sup>< \<triangleright> R1 S)))"
proof -
  have f1: "R2s P = P"
    by (meson Healthy_def assms(5))
  have f2: "R2s Q = Q"
    by (meson Healthy_def assms(6))
  have f3: "R2s R = R"
    by (meson Healthy_def assms(7))
  have "R2s S = S"
    by (meson Healthy_def assms(8))
  then show ?thesis
    using f3 f2 f1 by (simp add: RHS_design_composition assms(1) assms(2) assms(3) assms(4))
qed

lemma RH_design_export_R1: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R1(Q))"
  by pred_auto

lemma RH_design_export_R2s: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2s(Q))"
  by pred_auto

lemma RH_design_export_R2c: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2c(Q))"
  by pred_auto

lemma RHS_design_export_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R1(Q))"
  by pred_auto

lemma RHS_design_export_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2s(Q))"
  by pred_auto

lemma RHS_design_export_R2c: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2c(Q))"
  by pred_auto

lemma RHS_design_export_R2: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2(Q))"
  by pred_auto

lemma R1_design_R1_pre: 
  "\<^bold>R\<^sub>s(R1(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by pred_auto

lemma RHS_design_ok_wait: "\<^bold>R\<^sub>s(P\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile> Q\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by pred_auto

lemma RH_design_neg_R1_pre:
  "\<^bold>R ((\<not> R1 P) \<turnstile> R) = \<^bold>R ((\<not> P) \<turnstile> R)"
  by pred_auto

lemma RHS_design_neg_R1_pre:
  "\<^bold>R\<^sub>s ((\<not> R1 P) \<turnstile> R) = \<^bold>R\<^sub>s ((\<not> P) \<turnstile> R)"
  by pred_auto

lemma RHS_design_conj_neg_R1_pre:
  "\<^bold>R\<^sub>s (((\<not> R1 P) \<and> Q) \<turnstile> R) = \<^bold>R\<^sub>s (((\<not> P) \<and> Q) \<turnstile> R)"
  by pred_auto

lemma RHS_pre_lemma: "(\<^bold>R\<^sub>s P)\<^sup>f\<^sub>f = R1(R2c(P\<^sup>f\<^sub>f))"
  by pred_auto

lemma RH_design_R2c_pre:
  "\<^bold>R(R2c(P) \<turnstile> Q) = \<^bold>R(P \<turnstile> Q)"
  by pred_auto

lemma RHS_design_R2c_pre:
  "\<^bold>R\<^sub>s(R2c(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by pred_auto

subsection \<open> Refinement introduction laws \<close>

(* TODO: need equivalents to this lemma *)
lemma ex_unrest: "vwb_lens x \<Longrightarrow> $x \<sharp> P \<Longrightarrow> (\<Sqinter> x\<^sub>0. P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>) = P"
  apply (pred_auto)
  oops

lemma R1_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "$ok\<^sup>< \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>< \<sharp> P\<^sub>2" "$ok\<^sup>> \<sharp> P\<^sub>2"
    "$ok\<^sup>< \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>< \<sharp> Q\<^sub>2" "$ok\<^sup>> \<sharp> Q\<^sub>2"    
  shows "R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"

proof -
  have "R1((\<Sqinter> k k'. P\<^sub>1\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<turnstile> (\<Sqinter> k k'. P\<^sub>2\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>)) \<sqsubseteq> R1((\<Sqinter>k k'. Q\<^sub>1\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<turnstile> (\<Sqinter> k k'. Q\<^sub>2\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>)) 
       \<longleftrightarrow> `R1(\<Sqinter> k k'. P\<^sub>1\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<longrightarrow> R1(\<Sqinter> k k'. Q\<^sub>1\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>)` \<and> `R1(\<Sqinter> k k'. P\<^sub>1\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<and> R1(\<Sqinter> k k'. Q\<^sub>2\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>) \<longrightarrow> R1(\<Sqinter> k k'. P\<^sub>2\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>/ok\<^sup><,ok\<^sup>>\<rbrakk>)`"
    by (pred_auto, meson+)
  thus ?thesis
    sorry
    (* by (simp_all add: ex_unrest ex_plus Healthy_if assms) *)
qed

lemma R1_design_refine_RR:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
  shows "R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
  by (simp add: R1_design_refine assms unrest closure)

lemma RH_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "P\<^sub>1 is R2c" "P\<^sub>2 is R2c" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R2c"
    "$ok\<^sup>< \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>< \<sharp> P\<^sub>2" "$ok\<^sup>> \<sharp> P\<^sub>2"
    "$ok\<^sup>< \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>< \<sharp> Q\<^sub>2" "$ok\<^sup>> \<sharp> Q\<^sub>2"    
    "$wait\<^sup>< \<sharp> P\<^sub>1" "$wait\<^sup>< \<sharp> P\<^sub>2" "$wait\<^sup>< \<sharp> Q\<^sub>1" "$wait\<^sup>< \<sharp> Q\<^sub>2"    
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
proof -
  have "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> R1(R3c(R2c(P\<^sub>1 \<turnstile> P\<^sub>2))) \<sqsubseteq> R1(R3c(R2c(Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp add: R2c_R3c_commute RH_def)
  also have "... \<longleftrightarrow> R1(R3c(P\<^sub>1 \<turnstile> P\<^sub>2)) \<sqsubseteq> R1(R3c(Q\<^sub>1 \<turnstile> Q\<^sub>2))"
    by (simp add: Healthy_if R2c_design assms)
  also have "... \<longleftrightarrow> R1(R3c(P\<^sub>1 \<turnstile> P\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(R3c(Q\<^sub>1 \<turnstile> Q\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk>"
    apply pred_auto
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply (metis order_refl)
    done
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk>"      
    by pred_auto
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)"      
    by (simp add: usubst assms closure unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
    by (simp add: R1_design_refine assms)
  finally show ?thesis .
qed 

lemma RHS_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "P\<^sub>1 is R2c" "P\<^sub>2 is R2c" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R2c"
    "$ok\<^sup>< \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>< \<sharp> P\<^sub>2" "$ok\<^sup>> \<sharp> P\<^sub>2"
    "$ok\<^sup>< \<sharp> Q\<^sub>1" "$ok\<^sup>> \<sharp> Q\<^sub>1" "$ok\<^sup>< \<sharp> Q\<^sub>2" "$ok\<^sup>> \<sharp> Q\<^sub>2"    
    "$wait\<^sup>< \<sharp> P\<^sub>1" "$wait\<^sup>< \<sharp> P\<^sub>2" "$wait\<^sup>< \<sharp> Q\<^sub>1" "$wait\<^sup>< \<sharp> Q\<^sub>2"    
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> R1(R3h(R2c(P\<^sub>1 \<turnstile> P\<^sub>2))) \<sqsubseteq> R1(R3h(R2c(Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp add: R2c_R3h_commute RHS_def)
  also have "... \<longleftrightarrow> R1(R3h(P\<^sub>1 \<turnstile> P\<^sub>2)) \<sqsubseteq> R1(R3h(Q\<^sub>1 \<turnstile> Q\<^sub>2))"
    by (simp add: Healthy_if R2c_design assms)
  also have "... \<longleftrightarrow> R1(R3h(P\<^sub>1 \<turnstile> P\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(R3h(Q\<^sub>1 \<turnstile> Q\<^sub>2))\<lbrakk>False/wait\<^sup><\<rbrakk>"
    apply pred_auto
    apply metis
    apply metis
    apply metis
    apply metis
    apply metis
    apply (metis order_refl)
    done
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk> \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)\<lbrakk>False/wait\<^sup><\<rbrakk>"      
    by pred_auto
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)"      
    by (simp add: usubst assms closure unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<longrightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> P\<^sub>2`"
    by (simp add: R1_design_refine assms)
  finally show ?thesis .
qed 

lemma rdes_refine_intro:
  assumes "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqsubseteq> \<^bold>R(P\<^sub>2 \<turnstile> Q\<^sub>2)"
  by (simp add: RH_mono assms design_refine_intro)

lemma srdes_refine_intro:
  assumes "`P\<^sub>1 \<longrightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<longrightarrow> Q\<^sub>1`"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2)"
  by (simp add: RHS_mono assms design_refine_intro)

subsection \<open> Distribution laws \<close>

lemma RHS_design_choice: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqinter> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<or> Q\<^sub>2))"
  by (metis RHS_inf design_choice)

(* TODO: prove this *)
lemma RHS_design_sup: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<squnion> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> P\<^sub>2) \<turnstile> ((P\<^sub>1 \<longrightarrow> Q\<^sub>1) \<and> (P\<^sub>2 \<longrightarrow> Q\<^sub>2)))"
  oops

lemma RHS_design_USUP:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A. \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion> i \<in> A. P(i)) \<turnstile> (\<Sqinter> i \<in> A. Q(i)))"
  by (subst RHS_INF[OF assms, THEN sym], simp add: design_UINF_mem assms)

end