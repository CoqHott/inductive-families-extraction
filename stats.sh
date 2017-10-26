NB_LEMMAS=`grep '^Lemma' good_bad_ugly.v | wc -l`
NB_ADMITTED=`grep 'Admitted.' good_bad_ugly.v | wc -l`
NB_FAILED_LEMMAS=`grep '^Fail Lemma' good_bad_ugly.v | wc -l`
NB_DEF=`grep '^\(Definition\|Fixpoint\) ' good_bad_ugly.v | wc -l`
NB_FAILED_DEF=`grep '^Fail ' good_bad_ugly.v | grep -v '^Fail Lemma' | wc -l`

echo "Number of functions: $NB_DEF"
echo "Number of painful functions: $NB_FAILED_DEF"
echo "Number of lemmas: $NB_LEMMAS"
echo "Number of painful lemmas: $NB_ADMITTED"
echo "Number of unstated lemmas: $NB_FAILED_LEMMAS"
