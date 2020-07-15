import matplotlib
import ocaml
from matplotlib.backends.backend_agg import FigureCanvasAgg
from matplotlib._pylab_helpers import Gcf
from ocaml import ocaml_show
from io import BytesIO

matplotlib.interactive(True)

def send_fig_to_kernel(fig, fmt='png'):
    bytes_io = BytesIO()
    fig.canvas.print_figure(bytes_io, format=fmt, bbox_inches='tight')
    ocaml_show(bytes_io.getvalue())

def show(close=True, block=None):
    """Show all figures as PNG payloads sent to the Jupyter frontend.

    Parameters
    ----------
    close : Close figures after sending
    block : Not used.
    """
    for figure_manager in Gcf.get_all_fig_managers():
        fig = figure_manager.canvas.figure
        send_fig_to_kernel(fig)
    if close and Gcf.get_all_fig_managers():
        matplotlib.pyplot.close('all')

show._draw_called = False

def draw_if_interactive():
    if not matplotlib.is_interactive():
        return
    show._draw_called = True

def flush_figures():
    if show._draw_called:
        show(True)
        show._draw_called = False

FigureCanvas = FigureCanvasAgg

old_after_exec = ocaml.after_exec
def new_after_exec():
    old_after_exec()
    flush_figures()

ocaml.after_exec = lambda: new_after_exec()
