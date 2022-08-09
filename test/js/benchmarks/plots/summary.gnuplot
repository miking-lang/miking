# clear
# reset
# unset key
# # Make the x axis labels easier to read.
# set xtics rotate out
# # Select histogram data
# set style data histogram
# # Give the bars a plain fill pattern, and draw a solid line around them.
# set style fill solid border

set terminal png
set output "summary.png"
# Logarithmic scale on the y axis.
set title "Summary of benchmark results\nin logarithmic scale"
set xlabel "Benchmark"
set ylabel "Time (ms)"
set logscale y
set key under Left reverse

set style data histogram
set style histogram clustered gap 1
set style fill solid border -1
# set xtics rotate by -45 scale 0
set xtics rotate by -33
set grid y




# plot "summary.dat" using 2:xtic(1) t col, \
# 	 "summary.dat" using 3:xtic(1) t col, \

plot "summary.dat" using 4:xtic(1) t col, \
	 "summary.dat" using 5:xtic(1) t col, \
	 "summary.dat" using 6:xtic(1) t col, \
	 "summary.dat" using 7:xtic(1) t col, \


set terminal svg
set output "summary.svg"
replot
