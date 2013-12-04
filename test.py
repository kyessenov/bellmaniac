print "c"
T1 = c_alloc()
c(T1, 0, 0)
print T1
print "c1"
T2 = r_alloc()
r(T2, 0, 0)
c1(T2, 0, 0, n, w, T2, 0, 0, 0, 0, 0)
print T2
print array_equal(T1, T2)
