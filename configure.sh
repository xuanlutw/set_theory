make clean
rm -f _CoqProject
rm -f Makefile
rm -f Makefile.conf
echo '-arg -noinit' >  _CoqProject
echo '-R . zfc'     >> _CoqProject
echo Init/*.v       >> _CoqProject
echo Relation/Relation.v   >> _CoqProject
echo Relation/Function.v   >> _CoqProject
echo Relation/Utils.v      >> _CoqProject
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
