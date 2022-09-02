#!/bin/bash

# Create a .zip file containing all files needed for arXiv submission,
# for easy uploading

master_name=CT4P
bbl_file=${master_name}.bbl
bib_file=literature.bib

declare -a aux_files=("data.tex"
		      "monads.tex"
		      "solutions.tex"
		      "contravariant.tex"
		      "adjunctions.tex"
		      "forget-free.tex"
		     )
	 

latexmk -CA
latexmk -bibtex -pdf ${master_name}

current_date=$(date "+%F-%H-%M-%S")
submission_name="${current_date}-arxiv-submission"
submission_dir_name="${submission_name}-temp"

# create temporary directory of files for arXiv:
#rm -rf $submission_dir_name
mkdir -p ${submission_dir_name}
cp ${master_name}.tex ${submission_dir_name}/
cp ${bbl_file} ${submission_dir_name}/

for i in "${aux_files[@]}"
do
    cp $i ${submission_dir_name}/$i
    #latexpand --keep-includes --empty-comments sections/"$i" > ${submission_dir_name}/$i
    #meld sections/"$i" ${submission_dir_name}/sections/$i
done

# create zip archive
zip -r ${submission_name}.zip ${submission_dir_name}


# clean up temp directory
#rm -rf ${submission_dir_name}

cd ${submission_dir_name}
pdflatex ${master_name}
pdflatex ${master_name}
pdflatex ${master_name}
diffpdf ${master_name}.pdf ../${master_name}.pdf
