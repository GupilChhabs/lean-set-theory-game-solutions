apply Iff.intro
intro h1
apply compl_subset_compl_of_subset
exact h1
intro h1
have h2: Aᶜᶜ ⊆ Bᶜᶜ
apply compl_subset_compl_of_subset at h1
exact h1
rewrite [compl_compl] at h2
rewrite [compl_compl] at h2
exact h2
