## .latexmkrc
#
#$pdflatex = 'pdflatex --shell-escape %O %S';
#$pdf_mode = 1;
#
## Enable EPS to PDF conversion
#add_cus_dep('eps', 'pdf', 0, 'epstopdf');
#sub epstopdf {
#    system("epstopdf --outfile=\$$_[0]-eps-converted-to.pdf \$$_[0].eps");
#}
#