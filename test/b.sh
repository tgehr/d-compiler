RET=0
n=0
until [ ${RET} -eq 1 ]; do
    ../d bug.d
    RET=$?
    echo "$n"
    n=$(echo $n+1 | bc)
done