PAGE_NUM=1
LAST_PAGE=
LAST_NAME=
LAST_NUM=
LAST_ISA_DEF=
LAST_ISA_FILE=
ISA_ROOT="$1"
EXPECT=0
DONE=1

function find_isa_line_num() {
	if [[ ! -d "${ISA_ROOT}/${ISA_SESSION}" ]]; then
		return
	fi
	if [[ ! -f "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" ]]; then
		return
	fi
	if [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "definition ${LAST_ISA_DEF} ::")" ]]; then
		cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "definition ${LAST_ISA_DEF} ::" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "fun ${LAST_ISA_DEF} ::")" ]]; then
		cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "fun ${LAST_ISA_DEF} ::" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "locale ${LAST_ISA_DEF} =")" ]]; then
		cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "locale ${LAST_ISA_DEF} =" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "inductive ${LAST_ISA_DEF} ::")" ]]; then
                cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "inductive ${LAST_ISA_DEF} ::" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "inductive_set ${LAST_ISA_DEF} ::")" ]]; then
                cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "inductive_set ${LAST_ISA_DEF} ::" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "lemma ${LAST_ISA_DEF}\(\[.*\]\)\{0,1\}:")" ]]; then
		cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "lemma ${LAST_ISA_DEF}\(\[.*\]\)\{0,1\}:" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "theorem ${LAST_ISA_DEF}\(\[.*\]\)\{0,1\}:")" ]]; then
		cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "theorem ${LAST_ISA_DEF}\(\[.*\]\)\{0,1\}:" | cut -d':' -f 1
	elif [[ -n "$(cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "thm ${LAST_ISA_DEF}\(\[.*\]\)\{0,1\}:")" ]]; then
		cat "${ISA_ROOT}/${ISA_SESSION}/${ISA_THEORY}.thy" | grep -n "thm ${LAST_ISA_DEF}\(\[.*\]\)\{0,1\}:" | cut -d':' -f 1
	fi
}

function def_complete() {
	echo -n "Found ${LAST_NAME} ${LAST_NUM} on page ${LAST_PAGE}, " 1>&2
	if [[ -z "${LAST_ISA_DEF}" ]] || [[ -z "${LAST_ISA_FILE}" ]]; then
		echo "does not reference an Isabelle file." 1>&2
	else
		echo "references ${LAST_ISA_DEF} in ${LAST_ISA_FILE}." 1>&2
		ISA_SESSION="$(echo "${LAST_ISA_FILE}" | cut -d "." -f "1")"
		ISA_THEORY="$(echo "${LAST_ISA_FILE}" | cut -d "." -f "2")"
		ISA_LINE_NUM=$(find_isa_line_num)
		if [[ -z "${ISA_LINE_NUM}" ]]; then
			echo "- ${LAST_NAME} ${LAST_NUM} (page ${LAST_PAGE}): [${LAST_ISA_DEF}](${ISA_SESSION}/${ISA_THEORY}.thy) (line number missing!)"
		else
			echo "- ${LAST_NAME} ${LAST_NUM} (page ${LAST_PAGE}): [${LAST_ISA_DEF}](${ISA_SESSION}/${ISA_THEORY}.thy#L${ISA_LINE_NUM})"
		fi
	fi
}

echo "Start scanner..." 1>&2
echo "Now working on page ${PAGE_NUM}" 1>&2
while read LINE; do
	if [[ "${EXPECT}" == "1" ]]; then
		if [[ "$(echo "${LINE}" | grep -e '[A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}')" ]]; then
			LAST_ISA_FILE="$(echo "${LINE}" | grep -o -e '[A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}' | cut -d' ' -f 1)"
			EXPECT=0
			DONE=1
			def_complete
		fi
		continue
	fi
	if [[ "${EXPECT}" == "2" ]]; then
		if [[ "$(echo "${LINE}" | grep -e 'in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}')" ]]; then
			LAST_ISA_FILE="$(echo "${LINE}" | grep -o -e 'in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}' | cut -d' ' -f 2)"
			EXPECT=0
			DONE=1
			def_complete
		elif [[ "$(echo "${LINE}" | grep -e 'in')" ]]; then
			EXPECT=1
		fi
		continue
	fi
	if [[ "${EXPECT}" == "3" ]]; then
		if [[ "$(echo "${LINE}" | grep -e '[A-Za-z0-9_]\{1,\} in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}')" ]]; then
			LAST_ISA_DEF="$(echo "${LINE}" | grep -o -e '[A-Za-z0-9_]\{1,\} in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}' | cut -d' ' -f 1)"
			LAST_ISA_FILE="$(echo "${LINE}" | grep -o -e '[A-Za-z0-9_]\{1,\} in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}' | cut -d' ' -f 3)"
			EXPECT=0
			DONE=1
			def_complete
		elif [[ "$(echo "${LINE}" | grep -e '[A-Za-z0-9_]\{1,\} in')" ]]; then
			LAST_ISA_DEF="$(echo "${LINE}" | grep -o -e '[A-Za-z0-9_]\{1,\} in' | cut -d' ' -f 1)"
			EXPECT=1
		elif [[ "$(echo "${LINE}" | grep -e '[A-Za-z0-9_]\{1,\}')" ]]; then
			LAST_ISA_DEF="$(echo "${LINE}" | grep -o -e '[A-Za-z0-9_]\{1,\}')"
			EXPECT=2
		fi
		continue
	fi
	if [[ -n "$(echo "${LINE}" | grep -e $'Page [0-9][0-9]*')" ]]; then
		PAGE_NUM="$(echo "${LINE}" | grep -o -e 'Page [0-9][0-9]*' | grep -o -e '[0-9][0-9]*')"
		((PAGE_NUM++))
		echo "Now working on page ${PAGE_NUM}" 1>&2
	fi
	if [[ -n "$(echo "${LINE}" | grep -e 'Definition [0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]* [\(]')" ]]; then
		if [[ "${DONE}" == "0" ]]; then
			def_complete
		fi
		LAST_ISA_DEF=""
		LAST_ISA_FILE=""
		LAST_NUM="$(echo "${LINE}" | grep -o -e 'Definition [0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]* [\(]' | grep -o -e '[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*')"
		LAST_NAME="Definition"
		LAST_PAGE="${PAGE_NUM}"
		DONE=0
	fi
	if [[ -n "$(echo "${LINE}" | grep -e 'Theorem [0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]* [\(]')" ]]; then
		if [[ "${DONE}" == "0" ]]; then
			def_complete
		fi
		LAST_ISA_DEF=""
		LAST_ISA_FILE=""
		LAST_NUM="$(echo "${LINE}" | grep -o -e 'Theorem [0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]* [\(]' | grep -o -e '[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*')"
		LAST_NAME="Theorem"
		LAST_PAGE="${PAGE_NUM}"
		DONE=0
	fi
	if [[ -n "$(echo "${LINE}" | grep -e 'Lemma [0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]* [\(]')" ]]; then
		if [[ "${DONE}" == "0" ]]; then
			def_complete
		fi
		LAST_ISA_DEF=""
		LAST_ISA_FILE=""
		LAST_NUM="$(echo "${LINE}" | grep -o -e 'Lemma [0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]* [\(]' | grep -o -e '[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*')"
		LAST_NAME="Lemma"
		LAST_PAGE="${PAGE_NUM}"
		DONE=0
	fi
	if [[ -n "$(echo "${LINE}" | grep -e 'Also see')" ]]; then
		if [[ -n "$(echo "${LINE}" | grep -e 'Also see [A-Za-z0-9_]\{1,\} in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}')" ]]; then
			LAST_ISA_DEF="$(echo "${LINE}" | grep -o -e 'Also see [A-Za-z0-9_]\{1,\} in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}' | cut -d' ' -f 3)"
			LAST_ISA_FILE="$(echo "${LINE}" | grep -o -e 'Also see [A-Za-z0-9_]\{1,\} in [A-Za-z0-9_-]\{1,\}\.[A-Za-z0-9_-]\{1,\}' | cut -d' ' -f 5)"
			EXPECT=0
			DONE=1
			def_complete
		elif [[ -n "$(echo "${LINE}" | grep -e 'Also see [A-Za-z0-9_]\{1,\} in')" ]]; then
			LAST_ISA_DEF="$(echo "${LINE}" | grep -o -e 'Also see [A-Za-z0-9_]\{1,\} in' | cut -d' ' -f 3)"
			EXPECT=1
		elif [[ -n "$(echo "${LINE}" | grep -e 'Also see [A-Za-z0-9_]\{1,\}')" ]]; then
			LAST_ISA_DEF="$(echo "${LINE}" | grep -o -e 'Also see [A-Za-z0-9_]\{1,\}' | cut -d' ' -f 3)"
			EXPECT=2
		else
			EXPECT=3
		fi
	fi
done < <(pdftotext "$2" -)

echo "Scanning done" 1>&2
