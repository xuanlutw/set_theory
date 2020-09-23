make clean
rm -f _CoqProject
rm -f Makefile
rm -f Makefile.conf
echo '-arg -noinit' >  _CoqProject
echo '-R . zfc'     >> _CoqProject
echo Init/*.v       >> _CoqProject
echo Relation/*.v   >> _CoqProject
echo Structure/*.v  >> _CoqProject
echo Nat/*.v        >> _CoqProject
echo Ordinal/*.v    >> _CoqProject
echo Cardinal/*.v   >> _CoqProject
#echo int/*.v       >> _CoqProject
#echo rat/*.v       >> _CoqProject
#echo real/*.v      >> _CoqProject
coq_makefile -f _CoqProject -o Makefile
make
make gallinahtml
