ext x
apply Iff.intro
intro h1
rw [mem_inter_iff] at h1
rw [mem_inter_iff] at h1
rw [mem_inter_iff]
rw [mem_inter_iff]
constructor
exact h1.left.left
constructor
exact h1.left.right
exact h1.right
intro h
constructor
constructor
exact h.left
exact h.right.left
exact h.right.right
