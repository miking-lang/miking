reset
set title "Summary of benchmark results\nin logarithmic scale"
set xlabel "Benchmark" offset 0,-1
set ylabel "Time (ms)" rotate by 0 offset 10.5,17.5
set logscale y
set key under Left reverse

set style data histogram
set style histogram clustered gap 1
set style fill solid # border -1
set xtics rotate by 0 scale 0
set bmargin 8
set lmargin 8
set grid ytics linestyle 0

set boxwidth 0.85
fnt = "Helvetica,8"
bars = 8

START = 2
END = bars+1

align(sh) = ($0 - 1 + sh * (bars / 12.))

data = "summary.dat"
set terminal png size 1000,600 font "Helvetica,11"
set output "summary.png"

# plot data u 2:xtic(1) t col, \
# 	 data u 3:xtic(1) t col, \
#  	 data u 4:xtic(1) t col, \
# 	 data u 5:xtic(1) t col, \
# 	 data u 6:xtic(1) t col, \
# 	 data u 7:xtic(1) t col, \

plot for [COL=(START):(END)] data u COL:xtic(1) t col, \
    data u (align(-0.575)):2:2 w labels font fnt offset 0,0.5 t '', \
    data u (align(-0.4)):3:3 w labels font fnt offset 0,0.5 t '', \
    data u (align(-0.23)):4:4 w labels font fnt offset 0,0.5 t '', \
    data u (align(-0.07)):5:5 w labels font fnt offset 0,0.5 t '', \
    data u (align( 0.10)):6:6 w labels font fnt offset 0,0.5 t '', \
    data u (align( 0.25)):7:7 w labels font fnt offset 0,0.5 t '', \
    data u (align( 0.435)):8:8 w labels font fnt offset 0,0.5 t '', \
    data u (align( 0.60)):9:9 w labels font fnt offset 0,0.5 t ''

set terminal svg size 900,650 font "Helvetica,20"
set output "summary.svg"
fnt = "Helvetica,12"
set ylabel "Time (ms)" rotate by 0 offset 10.5,6
set bmargin 9
replot
