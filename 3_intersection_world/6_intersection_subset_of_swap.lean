intro x h
rewrite[mem_inter_iff]
rw [mem_inter_iff] at h
exact And.intro h.right h.left
