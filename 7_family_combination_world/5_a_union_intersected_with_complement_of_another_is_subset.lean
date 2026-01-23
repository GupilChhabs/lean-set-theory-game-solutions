intro x h
rw [mem_sUnion]
have hl:=h.left
have hr:=h.right
rw [mem_sUnion] at hl
obtain ⟨t,ht⟩ := hl
rw [mem_compl_iff] at hr
rw [mem_sUnion] at hr
push_neg at hr
apply Exists.intro t
constructor
constructor
exact ht.left
by_contra h2
rw [mem_compl_iff] at h2
push_neg at h2
have h3:= hr t h2
exact h3 ht.right
exact ht.right
