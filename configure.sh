make clean
rm -f _CoqProject
rm -f Makefile
echo '-arg -noinit' >  _CoqProject
echo '-R . zfc'     >> _CoqProject
echo Init/*.v       >> _CoqProject
#echo axiom/*.v     >> _CoqProject
#echo axiom/*.v     >> _CoqProject
#echo operation/*.v >> _CoqProject
#echo relation/*.v  >> _CoqProject
#echo nat/*.v       >> _CoqProject
#echo int/*.v       >> _CoqProject
#echo rat/*.v       >> _CoqProject
#echo real/*.v      >> _CoqProject
#echo order/*.v     >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
make
make gallinahtml
