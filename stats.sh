SRC=good_bad_ugly.v

NB_LEMMAS=`grep '^Lemma' $SRC | wc -l`
NB_ADMITTED=`grep 'Admitted.' $SRC | wc -l`
NB_FAILED_LEMMAS=`grep '^Fail Lemma' $SRC | wc -l`
NB_DEF=`grep '^\(Definition\|Fixpoint\) ' $SRC | wc -l`
NB_FAILED_DEF=`grep '^Fail ' $SRC | grep -v '^Fail Lemma' | wc -l`

echo "Number of functions: $NB_DEF"
echo "Number of painful functions: $NB_FAILED_DEF"
echo "Number of lemmas: $NB_LEMMAS"
echo "Number of painful lemmas: $NB_ADMITTED"
echo "Number of unstated lemmas: $NB_FAILED_LEMMAS"

echo ""
echo "Summary of failures: "
grep 'FAILED(' $SRC
