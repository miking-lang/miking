set title "Summary of benchmark results\nin logarithmic scale"
set xlabel "Benchmark"
set ylabel "Time (ms)"
set logscale y
set key under Left reverse

set style data histogram
set style histogram clustered gap 1
set style fill solid border -1
set xtics rotate by -33
set grid y

set terminal png
set output "summary.png"

data = "summary.dat"

plot data u 2:xtic(1) t col, \
	 data u 3:xtic(1) t col, \
 	 data u 4:xtic(1) t col, \
	 data u 5:xtic(1) t col, \
	 data u 6:xtic(1) t col, \
	 data u 7:xtic(1) t col, \

set terminal svg
set output "summary.svg"
replot
