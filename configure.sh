make clean
rm -f _CoqProject
rm -f Makefile
rm -f Makefile.conf
echo '-arg -noinit' >  _CoqProject
echo '-R . zfc'     >> _CoqProject
echo Init/*.v       >> _CoqProject
echo Relation/*.v   >> _CoqProject
echo Nat/Inductive.v       >> _CoqProject
echo Nat/Nature.v       >> _CoqProject
echo Nat/Recursion.v       >> _CoqProject
echo Nat/Nat_arith.v       >> _CoqProject
#echo int/*.v       >> _CoqProject
#echo rat/*.v       >> _CoqProject
#echo real/*.v      >> _CoqProject
#echo order/*.v     >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
make
make gallinahtml
