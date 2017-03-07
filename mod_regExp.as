/*
	mod_regExp
	
	HSP3用正規表現モジュール
	
	ver 1.2.0
*/

#define global DEBUGMODE

#ifdef DEBUGMODE
	#define global assertEx(%1)	assert (%1)
#else
	#define global assertEx(%1) if(0){}	//たぶん最適化で消える
#endif

#define global TRUE		1
#define global FALSE	0
#define global NULL		-1

#define global VARTYPE_MODULE	5

//演算子タイプ
	#enum global OC_INVALID=-1
	#enum global OC_SIMPLE	//単純文字列
	#enum global OC_ANY_ENG_LET	/*\w*/
	#enum global OC_NOT_ENG_LET	/*\W*/
	#enum global OC_ANY_SPACE	/*\s*/
	#enum global OC_NOT_SPACE	/*\S*/
	#enum global OC_ANY_DIGIT	/*\d*/
	#enum global OC_NOT_DIGIT	/*\D*/
	#enum global OC_ANY	//.
	#enum global OC_BOUND	/*\b*/
	#enum global OC_NOT_BOUND	/*B*/
	#enum global OC_LINEHEAD	//行頭
	#enum global OC_LINEEND	//行末
	#enum global OC_JOIN	//連結演算子
	#enum global OC_OR	//|
	#enum global OC_ZERO_OR_ONE	//?
	#enum global OC_ZERO_OR_MORE	//*?
	#enum global OC_ZERO_OR_MORE_GREEDY	//*
	#enum global OC_ONE_OR_MORE	//+?
	#enum global OC_ONE_OR_MORE_GREEDY	//+
	#enum global OC_N	//{n}
	#enum global OC_N_	//{n,}
	#enum global OC_NM	//{n,m}
	#enum global OC_SET	//文字集合
	#enum global OC_ANTI_SET	//除外文字集合
	#enum global OC_PACK	//(?:) 更に解析、分解され、最終的な構文木には残らない。
	#enum global OC_POSITIVE_LOOKAHEAD	//(?=)
	#enum global OC_NEGATIVE_LOOKAHEAD	//(?!)
	#enum global OC_CAPTURE	//キャプチャ
	#enum global OC_DUMMY

#module Capt_info_regExp count, idx, len	//キャプチャ情報クラス(Capt_infoクラス)
	/*
		count : キャプチャされた個数
		idx : キャプチャされた位置の配列
		len : キャプチャされた長さの配列
	*/
	tmp=0
	#modinit
		count=0 : idx=0 : len=0
		mref tmp,2
		return tmp
	
	#modcfunc local get_count
		return count
	#modcfunc local get_idx int id_	//id_ 番目のキャプチャ位置
		if ((id_<0)||(id_>=count)) {return -1}
		return idx(id_)
	#modcfunc local get_len int id_	//id_ 番目のキャプチャ長さ
		if ((id_<0)||(id_>=count)) {return -1}
		return len(id_)
	
	#modfunc local add int idx_, int len_
		assertEx ((idx_>=0)&&(len_>=0))
		idx(count)=idx_ : len(count)=len_
		count++
		return
#global

#module Node_regExp oc, string, n,m, addr_left, addr_right	//パターンの構文木のノードのクラス
	/*
		oc : 演算子
		
		string : 文字列
			oc=OC_SIMPLE の場合はその文字列
			oc=OC_SET, OC_ANTI_SET の場合はその文字集合
			それ以外の oc では必須ではないが、デバッグ時に木の中身を表示する可能性考えれば、相応しい文字列を入れておくのがよい。
		
		n,m : oc=OC_N, OC_N_, OC_NM の場合の n,m
			
		addr_left, addr_right : 左右のノードのアドレス(モジュール変数配列におけるインデックス)
			指すノードが無いときは NULL
	*/

	tmp=0
	
	#modcfunc local is_oc_known int oc_	//(デバッグ用)既知の演算子かどうか
		return ((oc_>=OC_INVALID)&&(oc_<OC_DUMMY))
	
	#modcfunc local node_exists int addr_	//(デバッグ用)そのノードが存在するか
		return node_exists@mod_regExp(addr_)
	
	#modinit int oc_, str string_, int n_,int m_, int addr_left_, int addr_right_
		assertEx (is_oc_known(thismod, oc_))
		#ifdef DEBUGMODE
			if ((oc_==OC_SIMPLE)||(oc_==OC_SET)||(oc_==OC_ANTI_SET)) {
				assertEx (string_!="")
			}
		#endif
		assertEx ((n_>=0)&&(m_>=0)&&(((oc_==OC_NM)&&(n_<=m_))||(oc_!=OC_NM)))
		assertEx ((addr_left_==NULL)||node_exists(thismod, addr_left_))
		assertEx ((addr_right_==NULL)||node_exists(thismod, addr_right_))
		
		oc=oc_
		string=string_
		n=n_ : m=m_
		addr_left=addr_left_
		addr_right=addr_right_
		mref tmp,2
		return tmp
	
	#modcfunc local get_oc
		return oc
	
	#modcfunc local get_string
		return string
	
	#modcfunc local get_n
		return n
	#modcfunc local get_m
		return m
	
	#modcfunc local get_addr_left
		return addr_left
	#modcfunc local get_addr_right
		return addr_right
	
	#modcfunc local is_char_in_set int char_, local flg	//その文字が文字集合に属するか？
		assertEx ((oc==OC_SET)||(oc==OC_ANTI_SET))
		
		flg=FALSE
		repeat strlen(string)
			if (char_==peek(string,cnt)) {flg=TRUE : break}
		loop
		return flg
#global

#module mod_regExp
	tree=0	//構文木
	addr_root=0	//根のアドレス
	
	#deffunc local clear_mod_var_array array array_	//モジュール変数配列をクリアする
		if (vartype(array_)!=VARTYPE_MODULE) {return}
		foreach array_ : delmod array_ : loop
		return
	
	#deffunc local init	//初期化
		control_char_set = '(',')', '{','}', '[',']', '\\', '^', '$', '|', '?', '+', '*', '.'	//制御文字集合
		return
	
	#defcfunc local is_number int char_//数字か？
		return (char_>='0')&&(char_<='9')
	
	#defcfunc local is_eng_letter int char_	//英単語を構成する1文字(a-zA-Z_0-9)か？
		return (((char_>='a')&&(char_<='z'))||((char_>='A')&&(char_<='Z'))||(char_=='_')||((char_>='0')&&(char_<='9')))
	
	#defcfunc local is_space int char_	//空白文字(半角スペース タブ \r \n)か？
		return ((char_==' ')||(char_=='\t')||(char_=='\r')||(char_==10))
	
	#defcfunc local is_control_char int char_, local flg	//制御文字か？
		flg=FALSE
		foreach control_char_set
			if (char_==control_char_set(cnt)) : flg=TRUE : break
		loop
		return flg
	
	#defcfunc local is_escaped_control_char int char_	//\ と合わせて制御文字になる(\d の d 等)か？
		return ((char_=='w')||(char_=='W')||(char_=='s')||(char_=='S')||(char_=='d')||(char_=='D')||(char_=='/')||(char_=='b')||(char_=='B'))
	
	#defcfunc local is_open_bracket int char_	//それは開き括弧か？
		return (char_=='(')||(char_=='{')||(char_=='[')
	
	#defcfunc local is_close_bracket int char_	//それは閉じ括弧か？
		return (char_==')')||(char_=='}')||(char_==']')
	
	#defcfunc local is_first_byte_of_zenkaku int char_	//全角文字の1バイト目かどうか
		return (((char_>=129)&&(char_<=159))||((char_>=224)&&(char_<=252)))
	
	#defcfunc local convert_escaped_char int char_	//\の次の１バイト分を変換して文字コードを返す
		switch char_
			case 't' : return '\t'
			case 'r' : return '\r'
			case 'n' : return 10
			default : return char_
		swend
		assertEx(FALSE)
		return
	
	#defcfunc local is_valid_sjis_string var string_, int left_, int right_, local flg, local left	//正常なSJIS文字列か？
		/*
			string_ : 解析対象文字列(変数)
			left_ : right_ : 解析開始,終了位置(終了位置は解析対象に含まれない)
		*/
		assertEx((left_>=0)&&(right_>=0)&&(left_<=right_))
		assertEx(right_<=strlen(string_))
		
		flg=TRUE
		left=left_
		repeat
			if (left==right_) {break}
			if (is_first_byte_of_zenkaku(peek(string_, left))) {
				if (left==right_-1) {flg=FALSE : break}
				left+=2
				continue
			}
			left++
		loop
		return flg
	
	#defcfunc local dont_need_left_operand int oc_	//左オペランド不要か?
		return ((oc_==OC_SIMPLE)||(oc_==OC_ANY_ENG_LET)||(oc_==OC_NOT_ENG_LET)||(oc_==OC_ANY_SPACE)||(oc_==OC_NOT_SPACE)||(oc_==OC_ANY_DIGIT)||(oc_==OC_NOT_DIGIT)||(oc_==OC_ANY)||(oc_==OC_BOUND)||(oc_==OC_NOT_BOUND)||(oc_==OC_LINEHEAD)||(oc_==OC_LINEEND)||(oc_==OC_SET)||(oc_==OC_ANTI_SET)||(oc_==OC_PACK)||(oc_==OC_POSITIVE_LOOKAHEAD)||(oc_==OC_NEGATIVE_LOOKAHEAD)||(oc_==OC_CAPTURE))

	#defcfunc local node_exists int addr_	//(デバッグ用)そのノードが存在するか
		if (addr_==NULL) {return FALSE}
		return varuse(tree(addr_))
	
	#defcfunc local find_close_bracket var tgt_, int code_, int left_, int right_, int char_set_mode_, local char_set_mode, local left, local idx, local depth, local char	//対応する閉じ括弧の検索
		/*
			tgt_ : ターゲット文字列(変数)
			code_ : 閉じ括弧の文字コード
			left_, right_ : 検索開始位置(開き括弧の右隣), 検索終了位置(終了位置は解析対象に含まれない)
			char_set_mode_ : [] 内モードフラグ。[]内モードでは [(){}を普通の文字と同列に扱う。
			
			[戻り値]
				(-1,other) : (無い, 発見位置)
		*/
		assertEx (is_close_bracket(code_))
		assertEx ((left_>=0)&&(right_>=0)&&(left_<=right_))
		assertEx (right_<=strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		
		char_set_mode=char_set_mode_
	
		idx=-1 : depth=1 : left=left_
		repeat
			if (left==right_) {break}
			char=peek(tgt_, left)
			
			if (char=='\\') {
				if (left==right_-1) {break}	//\ の右が空
				left+=2
				continue
			}
			if (char_set_mode) {
				if (char==']') {
					if ((depth==1)&&(code_==']')) {idx=left : break}
					depth--
					char_set_mode=FALSE
				}
				left++
				continue
			}
			if (is_first_byte_of_zenkaku(char)) {left+=2 : continue}
			if (char=='[') {
				depth++
				char_set_mode=TRUE
				left++
				continue
			}
			if (is_open_bracket(char)) {depth++}
			if ((depth==1)&&(char==code_)) {idx=left : break}
			if (is_close_bracket(char)) {depth--}
			left++
		loop
		return idx
	
	#defcfunc local parse_in_braces var tgt_, int left_, int right_, var n_, var m_, var errIdx_, local flg_error, local left, local left2, local char	//{}内のパース
		/*
			tgt_ : ターゲット文字列(変数)
			left_, right_ : パース開始位置({の右隣),終了位置(}の位置)
			n_, m_ : 読み取った {n,m} の n,m (int)を保存
			errIdx_ : (構文エラーのとき)エラーを見つけた位置を保存
			
			[戻り値]
				OC_INVALID, OC_N, OC_N_, OC_NM のいずれか
			
			[備考]
				{}の中には半角数字か,のみの存在を許す
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		assertEx ((peek(tgt_, left_-1)=='{')&&(peek(tgt_, right_)=='}'))
		
		flg_error=FALSE
		
		//n を得る
		left=left_
		repeat
			if (left==right_) {break}
			char=peek(tgt_, left)
			if (char==',') {
				if (left==left_) {flg_error=TRUE}	//, の左が空
				break
			}
			if (is_number(char)==FALSE) {flg_error=TRUE : break}
			left++
		loop
		if (flg_error) {errIdx_=left : return OC_INVALID}
		
		//この時点で , が1つあった場合は left はその位置で止まっている。
		//, が無かった場合は left==right_ が成立
		n_=int(strmid(tgt_, left_, left-left_))
		if (left==right_) {return OC_N}
		if (left==right_-1) {return OC_N_}
		//この時点で left+2 <= right_ が成立
		
		//mを得る
		left2=left+1	//さっきの, の右隣に移動
		repeat
			if (left2==right_) {break}
			char=peek(tgt_, left2)
			if (is_number(char)==FALSE) {flg_error=TRUE : errIdx_=left2 : break}
			left2++
		loop
		if (flg_error) {return OC_INVALID}
		m_=int(strmid(tgt_, left+1, right_-left+1))
		if (n_>m_) {errIdx_=left+1 : return OC_INVALID}
		
		return OC_NM
	
	#defcfunc local parse_in_boxBrackets var tgt_, int left_, int right_, var charSet_, var errIdx_, local oc, local left, local left2, local char, local c1, local c2, local strbuf, local c	//[]内のパース
		/*
			tgt_ : ターゲット文字列(変数)
			left_, right_ : パース開始,終了位置
			charSet_ : 読み取った文字集合を保存
			errIdx_ : (構文エラーのとき)エラーを見つけた位置を保存
			
			[戻り値]
				OC_INVALID, OC_SET, OC_ANTI_SET のいずれか
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		assertEx ((peek(tgt_, left_-1)=='[')&&(peek(tgt_, right_)==']'))
		
		//OC_SET か OC_ANTI_SET か判別
		char=peek(tgt_, left_)
		left=left_
		if (char=='^') {oc=OC_ANTI_SET : left++} else {oc=OC_SET}
		if (left==right_) {return OC_INVALID}
	
		//集合取得
		charSet_=""
		left2=left
		repeat
			if (left2==right_) {break}
			char=peek(tgt_, left2)
			if (char='\\') {
				if (left2==right_-1) {oc=OC_INVALID : errIdx_=left2 : break}	//\の右が空
				strbuf="" : poke strbuf, 0, convert_escaped_char(peek(tgt_, left2+1))
				charSet_+=strbuf
				left2+=2
				continue
			}
			if (char=='-') {
				if ((left2==left)||(left2==right_-1)) {charSet_+="-" : left2++ : continue}	//ただの-扱い
				
				//文字コード範囲指定
				poke charSet_, strlen(charSet_)-1, 0	//直前に登録した文字を取り消す
				c1=peek(tgt_, left2-1) : c2=peek(tgt_, left2+1)
				if (c1>c2) {oc=OC_INVALID : errIdx_=left2 : break}
				sdim strbuf, c2-c1+2 : c=c1 : repeat c2-c1+1 : poke strbuf, cnt, c : c++ : loop
				charSet_+=strbuf
				left2+=2
				continue
			}
			charSet_+=strmid(tgt_, left2, 1)
			left2++
		loop
		
		return oc
	
	#defcfunc local is_simplifiable var tgt_, int left_, int right_, local flg, local left, local char	//簡約化可能か？
		/*
			tgt_ : 正規表現パターン全文(変数)
			left_, right_ : 解析開始,終了位置(終了位置は解析対象に含まれない)
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<=strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		
		flg=TRUE : left=left_
		repeat
			if (left==right_) {break}
			char=peek(tgt_, left)
			if (is_first_byte_of_zenkaku(char)) {left+=2 : continue}
			if (char=='\\') {
				if (left==right_-1) {flg=FALSE : break}	//\ の右側が空
				//\ の右側を調べる
				char=peek(tgt_, left+1)
				if (is_escaped_control_char(char)) {flg=FALSE : break}
				if (is_first_byte_of_zenkaku(char)) {left+=3} else {left+=2}
				continue
			}
			if (is_control_char(char)) {	//\ 以外の制御文字
				switch char
					case '^'
						if (left==0) {flg=FALSE : break}	//OC_LINEHEAD
						swbreak
					case '$'
						if (left==strlen(tgt_)-1) {flg=FALSE : break}	//OC_LINEEND
						swbreak
					default
						flg=FALSE : break
				swend
				left++
				continue
			}
			//上記以外の文字
			left++
		loop
		return flg
	
	#defcfunc local simplify var tgt_, int left_, int right_, local string_simplified, local len_simplified, local left, local char	//簡約化。エスケープシーケンスを消化する。
		/*
			tgt_ : 正規表現パターン全文(変数)
			left_, right_ : 簡約化開始,終了位置(終了位置は解析対象に含まれない)
			
			[戻り値]
				簡約化後の文字列
			
			[備考]
				入力が簡約化可能であると仮定している
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<=strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		assertEx (is_simplifiable(tgt_, left_, right_))
		
		sdim string_simplified, strlen(tgt_)+1 : len_simplified=0
		left=left_
		repeat
			if (left==right_) {break}
			char=peek(tgt_, left)
			if (is_first_byte_of_zenkaku(char)) {
				poke string_simplified, len_simplified, char
				poke string_simplified, len_simplified+1, peek(tgt_, left+1)
				len_simplified+=2
				left+=2 : continue
			}
			if (char=='\\') {
				char=peek(tgt_, left+1)	//※\ の右側は空でない(∵簡約化可能)
				if (is_first_byte_of_zenkaku(char)) {left++ : continue}
				poke string_simplified, len_simplified, convert_escaped_char(char) : len_simplified++
				left+=2 : continue
			}
			//上記以外の文字
			poke string_simplified, len_simplified, char : len_simplified++
			left++
		loop
		return string_simplified
	
	#defcfunc local get_one_simplifiable_string var tgt_, int left_, int right_, var simplified_string_, var errIdx_, local flg_error, local flg_stop, local left, local delta_left_prev, local byte_len_simplified, local char_count_simplified, local is_prev_zenkaku, local char	//一番左側の簡約化可能文字列を取得
		/*
			tgt_ : 正規表現パターン全文(変数)
			left_, right_ : 解析開始,終了位置(終了位置は解析対象に含まれない)
			simplified_string_ : 簡約化後の文字列を保存
			errIdx_ : (構文エラーのとき)エラー発見位置
			
			[戻り値]
				(-1,0,larger) : (構文エラー, 該当なし, 検出した簡約化可能文字列(tgt_内)の長さ)
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<=strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		
		flg_error=FALSE
		sdim simplified_string_, strlen(tgt_)+1
		left=left_
		delta_left_prev=0	//直前の left の増分
		byte_len_simplified=0 : char_count_simplified=0	//簡約化後文字列のバイト長, 文字数
		is_prev_zenkaku=FALSE//直前に調べた文字が全角かどうか
		repeat
			if (left==right_) {break}
			char=peek(tgt_, left)
			
			//全角文字
			if (is_first_byte_of_zenkaku(char)) {
				poke simplified_string_, byte_len_simplified, char
				poke simplified_string_, byte_len_simplified+1, peek(tgt_, left+1)
				byte_len_simplified+=2 : char_count_simplified++ : is_prev_zenkaku=TRUE
				left+=2 : delta_left_prev=2
				continue
			}
			
			//\
			if (char=='\\') {
				if (left==right_-1) {flg_error=TRUE : errIdx_=left : break}	//\ の右が空
				char=peek(tgt_, left+1)
				if (is_first_byte_of_zenkaku(char)) {left++ : delta_left_prev=1 : continue}
				if (is_escaped_control_char(char)) {break}
				char=convert_escaped_char(char)
				poke simplified_string_, byte_len_simplified, char
				byte_len_simplified++ : char_count_simplified++ : is_prev_zenkaku=FALSE
				left+=2 : delta_left_prev=2
				continue
			}
			
			//\以外の制御文字
			if (is_control_char(char)) {
				switch char
					case '^'
						if (left==0) {break}	//OC_LINEHEAD
						swbreak
					case '$'
						if (left==strlen(tgt_)-1) {break}	//OC_LINEEND
						swbreak
					default
						if ((char=='?')||(char=='*')||(char=='+')||(char=='{')) {	//左オペランド必須の演算子
							//左隣の1文字をこの演算子に割り当てる
							if (char_count_simplified>=2) {	//char の左に2文字以上ある場合はその右端の1文字を切り離して char に充てる
								if (is_prev_zenkaku) {
									wpoke simplified_string_, byte_len_simplified-2,0
									byte_len_simplified-=2
								} else {
									poke simplified_string_, byte_len_simplified-1, 0
									byte_len_simplified-=1
								}
								char_count_simplified--
								left-=delta_left_prev
							}
						}
						break
				swend
				poke simplified_string_, byte_len_simplified, char
				byte_len_simplified++ : char_count_simplified++ : is_prev_zenkaku=FALSE
				left++ : delta_left_prev=1
				continue
			}
			
			//上記以外の文字
			poke simplified_string_, byte_len_simplified, char
			byte_len_simplified++ : char_count_simplified++ : is_prev_zenkaku=FALSE
			left++ : delta_left_prev=1
		loop
		
		if (flg_error) {return -1}
		return left-left_
	
	#defcfunc local get_one_oc	var tgt_, int left_, int right_, var len_, var node_, var errIdx_, local len_left_simple_string, local simplified_string, local char, local right2, local oc, local n, local m, local strbuf//一番優先順位の低いオペコード(オペランドも含む)を取得
		/*
			tgt_ : 正規表現パターン全文(変数)
			left_, right_ : 解析開始,終了位置(終了位置は解析対象に含まれない)。見つけたオペコードの位置は常に left_ になる。
			len_ : 見つけたオペコードの長さ(tgt_ 上)を保存
			node_ : (構文が正常なとき)Node_regExp 型の変数を保存。ここにオペコードの情報を入れて返す。(varuse(node)==FALSE を仮定)
			errIdx_ : (構文エラーのとき)エラーを見つけた位置
			
			[戻り値]
				演算子タイプのいずれか
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<=strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		
		//左に簡約化可能文字列があるかないかが重要
		len_left_simple_string=get_one_simplifiable_string(tgt_, left_, right_, simplified_string, errIdx_)
		if (len_left_simple_string==-1) {return OC_INVALID}
		if (len_left_simple_string>=1) {
			len_=len_left_simple_string
			newmod node_, Node_regExp, OC_SIMPLE, simplified_string, 0,0, NULL,NULL
			return OC_SIMPLE
		}
			char=peek(tgt_, left_)	//必ず制御文字
			switch char
				case '('
					//対応する ) を探す
					right2=find_close_bracket(tgt_, ')', left_+1, right_, FALSE)
					if (right2==-1) {errIdx_=left_ : return OC_INVALID}
					len_=right2+1-left_
					if (len_<=2) {errIdx_=left_ : return OC_INVALID}	//中身が空
					
					//( ), (?:), (?=), (?!) のどれか?
					char=peek(tgt_, left_+1)
					if (char=='?') {
						if (len_<=4) {errIdx_=left_+1 : return OC_INVALID}	//(?), (?:), (?=) 等
						char=peek(tgt_, left_+2)
						switch char
							case ':' : oc=OC_PACK : swbreak
							case '=' : oc=OC_POSITIVE_LOOKAHEAD : swbreak
							case '!' : oc=OC_NEGATIVE_LOOKAHEAD : swbreak
							default
								errIdx_=left_+2 : return OC_INVALID
						swend
						newmod node_, Node_regExp, oc, strmid(tgt_, left_, len_), 0,0, NULL,NULL
						return oc
					}
					newmod node_, Node_regExp, OC_CAPTURE, strmid(tgt_, left_, len_), 0,0, NULL,NULL
					return OC_CAPTURE
				case '{'
					//対応する } を探す
					right2=find_close_bracket(tgt_, '}', left_+1, right_, FALSE)
					if (right2==-1) {errIdx_=left_ : return OC_INVALID}
					en_=right2+1-left_
					if (len_<=2) {errIdx_=left_ : return OC_INVALID}	//中身が空
					
					oc=parse_in_braces(tgt_, left_+1, right2, n,m, errIdx_)
					if (oc==OC_INVALID) {return OC_INVALID}
					newmod node_, Node_regExp, oc, strmid(tgt_, left_, len_), n,m, NULL,NULL
					return oc
				case '['
					//対応する ] を探す
					right2=find_close_bracket(tgt_, ']', left_+1, right_, TRUE)
					if (right2==-1) {errIdx_=left_ : return OC_INVALID}
					len_=right2+1-left_
					if (len_<=2) {errIdx_=left_ : return OC_INVALID}	//中身が空
					
					oc=parse_in_boxBrackets(tgt_, left_+1, right2, strbuf, errIdx_)
					if (oc==OC_INVALID) {return OC_INVALID}
					newmod node_, Node_regExp, oc, strbuf, 0,0, NULL, NULL
					return oc
				case '\\'
					//\ の右が空でないことは get_one_simplifiable_string() により保証されている
					//簡約化不可能、つまり制御構文であることは保証されている
					
					char=peek(tgt_, left_+1)
					switch char
						case 'w' : oc=OC_ANY_ENG_LET : strbuf="w" : swbreak
						case 'W' : oc=OC_NOT_ENG_LET : strbuf="W" : swbreak
						case 's' : oc=OC_ANY_SPACE : strbuf="s" : swbreak
						case 'S' : oc=OC_NOT_SPACE : strbuf="S" : swbreak
						case 'd' : oc=OC_ANY_DIGIT : strbuf="d" : swbreak
						case 'D' : oc=OC_NOT_DIGIT : strbuf="D" : swbreak
						case 'b' : oc=OC_BOUND : strbuf="b" : swbreak
						case 'B' : oc=OC_NOT_BOUND : strbuf="B" : swbreak
						default : assertEx (FALSE)
					swend
					len_=2
					newmod node_, Node_regExp, oc, strbuf, 0,0, NULL,NULL
					return oc
				case '.'
					len_=1 : newmod node_, Node_regExp, OC_ANY, ".", 0,0, NULL,NULL
					return OC_ANY
				case '^'
					len_=1 : newmod node_, Node_regExp, OC_LINEHEAD, "^", 0,0, NULL,NULL
					return OC_LINEHEAD
				case '$'
					len_=1 : newmod node_, Node_regExp, OC_LINEEND, "$", 0,0, NULL,NULL
					return OC_LINEEND
				case '|'
					if (left_==right_-1) {errIdx_=left_ : return OC_INVALID}	//右が空
					len_=1 : newmod node_, Node_regExp, OC_OR, "|", 0,0, NULL,NULL
					return OC_OR
				case '?'
					len_=1 : newmod node_, Node_regExp, OC_ZERO_OR_ONE, "?", 0,0, NULL,NULL
					return OC_ZERO_OR_ONE
				case '*'
					if (left_==right_-1) {
						oc=OC_ZERO_OR_MORE_GREEDY : len_=1  : strbuf="*"
					} else {
						char=peek(tgt_, left_+1)
						if (char=='?') {
							oc=OC_ZERO_OR_MORE : len_=2 : strbuf="*?"
						} else {oc=OC_ZERO_OR_MORE_GREEDY : len_=1 : strbuf="*"}
					}
					newmod node_, Node_regExp, oc, strbuf, 0,0, NULL,NULL
					return oc
				case '+'
					if (left_==right_-1) {
						oc=OC_ONE_OR_MORE_GREEDY : len_=1 : strbuf="+"
					} else {
						char=peek(tgt_, left_+1)
						if (char=='?') {
							oc=OC_ONE_OR_MORE : len_=2 : strbuf="+?"
						} else {oc=OC_ONE_OR_MORE_GREEDY : len_=1 : strbuf="+"}
					}
					newmod node_, Node_regExp, oc, strbuf, 0,0, NULL,NULL
					return oc
				default
					errIdx_=left_ : return OC_INVALID
			swend
		
		assert (FALSE)
		return
	
	#deffunc local delete_tree_ int addr_, local addr_left, local addr_right	//delete_tree から呼ばれる再帰関数
		/*
			addr_ : ノードのアドレス。そのノード以下を破棄する
		*/
		assertEx (varuse(tree(addr_)))
		
		addr_left=get_addr_left@Node_regExp(tree(addr_))
		addr_right=get_addr_right@Node_regExp(tree(addr_))
		if (addr_left!=NULL) {delete_tree_ addr_left}
		if (addr_right!=NULL) {delete_tree_ addr_right}
		delmod tree(addr_)
		return
		
	#deffunc local delete_tree	//構文木を破棄
		if (addr_root==NULL) {return}
		if (vartype(tree)!=VARTYPE_MODULE) {return}
		if (varuse(tree(addr_root))==FALSE) {return}
		delete_tree_ addr_root
		return
	
	#defcfunc local build_tree var tgt_, int left_, int right_, var errIdx_, local oc1, local oc2, local oc3, local len1, local len2, local len3, local node1, local node2, local node3, local left, local right, local addr_left, local addr_right, local strbuf	//構文木作成。regExp_setPat() から呼ばれる再帰関数
		/*
			tgt_ : 正規表現パターン全文(変数)
			left_, right_ : 解析開始,終了位置(終了位置は解析対象に含まれない)
			errIdx_ : (構文エラーのとき)エラー発見位置を保存
			
			[戻り値]
				失敗したとき(構文エラー)は NULL。
				成功したときは tgt_ を 左オペランド+演算子+右オペランド に分解したときの演算子ノードのアドレス。
				左,右オペランドは空になることもある。
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<right_))
		assertEx (right_<=strlen(tgt_))
		assertEx (is_valid_sjis_string(tgt_, left_, right_))
		
		oc1=get_one_oc(tgt_, left_, right_, len1, node1, errIdx_) : if (oc1==OC_INVALID) {return NULL}	//1つ目のオペコード
		
		//左オペランド必須の演算子ならエラー
		if (dont_need_left_operand(oc1)==FALSE) {
			errIdx_=left_ : return NULL
		}
		
		if (left_+len1==right_) {	//oc1より右にオペコードが無い
			//自身が葉ノードになるパターン
			if (is_simplifiable(tgt_, left_, right_)) {
				newmod tree, Node_regExp, OC_SIMPLE, simplify(tgt_, left_, right_), 0,0, NULL,NULL
				return stat
			}
			if (dont_need_left_operand(oc1)) {
				switch oc1
					case OC_PACK
						return build_tree(tgt_, left_+3, right_-1, errIdx_)
					case OC_POSITIVE_LOOKAHEAD
						addr_left=build_tree(tgt_, left_+3, right_-1, errIdx_)
						if (addr_left==NULL) {return NULL}
						newmod tree, Node_regExp, oc1, "(?=)", 0,0, addr_left,NULL
						return stat
					case OC_NEGATIVE_LOOKAHEAD
						addr_left=build_tree(tgt_, left_+3, right_-1, errIdx_)
						if (addr_left==NULL) {return NULL}
						newmod tree, Node_regExp, oc1, "(?!)", 0,0, addr_left,NULL
						return stat
					case OC_CAPTURE
						addr_left=build_tree(tgt_, left_+1, right_-1, errIdx_)
						if (addr_left==NULL) {return NULL}
						newmod tree, Node_regExp, oc1, "()", 0,0, addr_left,NULL
						return stat
					default
						newmod tree, Node_regExp, oc1, get_string@Node_regExp(node1), 0,0, NULL,NULL
						return stat
				swend
				assertEx (FALSE)
			}
			assertEx (FALSE)
		} else {
			left=left_+len1
			oc2=get_one_oc(tgt_, left, right_, len2, node2, errIdx_) :  : if (oc2==OC_INVALID) {return NULL}	//2つ目のオペコード
			
			//(この時点で oc2!=OC_LINEHEAD が成立)
			
			//自身が連結演算子になるパターン
			if (dont_need_left_operand(oc2)) {
				addr_left=build_tree(tgt_, left_, left, errIdx_) : if (addr_left==NULL) {return NULL}
				addr_right=build_tree(tgt_, left, right_, errIdx_) : if (addr_right==NULL) {delete_tree_ addr_left : return NULL}
				newmod tree, Node_regExp, OC_JOIN, "<->", 0,0, addr_left,addr_right
				return stat
			}
			
			//oc2 が演算子になるパターン(この時点で oc2 は左オペランド必須と確定)
			addr_left=build_tree(tgt_, left_, left, errIdx_) : if (addr_left==NULL) {return NULL}
			if (left+len2==right_) {	//oc2 より右にオペコードが無い
				addr_right=NULL
			} else {
				addr_right=build_tree(tgt_, left+len2, right_, errIdx_)
				if (addr_right==NULL) {delete_tree_ addr_left : return NULL}
			}
			newmod tree, Node_regExp, oc2, get_string@Node_regExp(node2), get_n@Node_regExp(node2), get_m@Node_regExp(node2), addr_left, addr_right
			return stat
		}
		assertEx (FALSE)
	
	#deffunc local show_tree_ int addr_, int depth_, local thisnode, local addr_left, local addr_right, local strbuf	//show_tree から呼ばれる再帰関数
		/*
			addr_ : ノードのアドレス。そのノード以下を表示する
			depth_ : ノードの深さ
		*/
		assertEx (varuse(tree(addr_)))
		dup thisnode, tree(addr_)
		
		//自身の string を表示
		strbuf="" : repeat depth_ : strbuf+="  " : loop
		mes strbuf+get_string@Node_regExp(thisnode)
		
		//子ノードを表示
		addr_left=get_addr_left@Node_regExp(thisnode)
		addr_right=get_addr_right@Node_regExp(thisnode)
		if (addr_left!=NULL) {show_tree_ addr_left, depth_+1}
		if (addr_right!=NULL) {show_tree_ addr_right, depth_+1}
		return
	
	#deffunc local show_tree	//(デバッグ用)構文木の全体像を表示
		assertEx (vartype(tree)==VARTYPE_MODULE)
		assertEx (varuse(tree(addr_root)))
		show_tree_ addr_root, 0
		return
		
	#defcfunc regExp_setPat str pat_, var errIdx_, local pat	//パターンをセット
		/*
			pat_ : パターン文字列
			errIdx_ : (構文エラーのとき)エラーを見つけた位置を保存
			
			[戻り値]
				(TRUE,FALSE) : (成功,構文エラー)
		*/
		if (strlen(pat_)==0) {errIdx_=0 : return FALSE}
		
		delete_tree	//掃除
		pat=pat_
		if (is_valid_sjis_string(pat, 0, strlen(pat))==FALSE) {errIdx_=strlen(pat)-1 : return FALSE}
		addr_root=build_tree(pat, 0, strlen(pat), errIdx_)
		return (addr_root!=NULL)
	
	#defcfunc local tree_exists	//構文木が構築済みか？
		if (vartype(tree)!=VARTYPE_MODULE) {return FALSE}
		if (varuse(tree(addr_root))) {return TRUE}
		return FALSE
	
	#defcfunc local match_ var tgt_, int left_, int right_, int addr_, var capt_info_, local thisnode, local oc, local strbuf, local char, local addr_left, local addr_right, local len_match_left, local len_match_right, local len_match, local left, local best_record_left2, local best_record_len_match_right, local count_match	//regExp_match() から呼ばれる再帰関数
		/*
			tgt_ : ターゲット文字列全文
			left_, right_ : 判定開始,終了位置(終了位置は解析対象に含まれない)
			addr_ : 構文木のノードのアドレス
			capt_info_ : Capt_info 型モジュール変数。初期化して渡すこと。
			
			[動作]
				addr_ ノード以下が tgt_ の left_ の位置でマッチするかどうか調べる
			
			[戻り値]
				(-1,larger) : (一致なし, 一致した長さ)
		*/
		assertEx ((left_>=0)&&(right_>=0)&&(left_<=right_))	//行末の $ オペレータに対しては left_==right_ となり得る
		assertEx (right_<=strlen(tgt_))
		
		dup thisnode, tree(addr_)
		oc=get_oc@Node_regExp(thisnode)
		assertEx (oc!=OC_INVALID)
		
		//自身が葉ノードであるパターン
			switch oc
				case OC_SIMPLE
					if (left_==right_) {return -1}
					strbuf=get_string@Node_regExp(thisnode)
					if (strlen(strbuf)>right_-left_) {return -1}
					if (0==instr(tgt_, left_, strbuf)) {return strlen(strbuf)}
					return -1
				case OC_ANY_ENG_LET
					if (left_==right_) {return -1}
					if (is_eng_letter(peek(tgt_, left_))) {return 1}
					return -1
				case OC_NOT_ENG_LET
					if (left_==right_) {return -1}
					if (is_eng_letter(peek(tgt_, left_))) {return -1}
					return 1
				case OC_ANY_SPACE
					if (left_==right_) {return -1}
					if (is_space(peek(tgt_, left_))) {return 1}
					return -1
				case OC_NOT_SPACE
					if (left_==right_) {return -1}
					if (is_space(peek(tgt_, left_))) {return -1}
					return 1
				case OC_ANY_DIGIT
					if (left_==right_) {return -1}
					if (is_number(peek(tgt_, left_))) {return 1}
					return -1
				case OC_NOT_DIGIT
					if (left_==right_) {return -1}
					if (is_number(peek(tgt_, left_))) {return -1}
					return 1
				case OC_BOUND
					if (left_==right_) {return 0}
					if (is_space(peek(tgt_, left_))) {return 1}
					return -1
				case OC_NOT_BOUND
					if (left_==right_) {return -1}
					if (is_space(peek(tgt_, left_))) {return -1}
					return 1
				case OC_ANY
					if (left_==right_) {return -1}
					if (is_first_byte_of_zenkaku(peek(tgt_, left_))) {return 2}
					return 1
				case OC_LINEHEAD
					if (left_==0) {return 0}
					if (peek(tgt_, left_-1)==10) {return 0}
					return -1
				case OC_LINEEND
					if (left_==right_) {return 0}
					char=peek(tgt_, left_)
					if ((char=='\r')||(char==10)) {return 0}
					return -1
				case OC_SET
					if (left_==right_) {return -1}
					if (is_char_in_set@Node_regExp(thisnode, peek(tgt_, left_))) {return 1}
					return -1
				case OC_ANTI_SET
					if (left_==right_) {return -1}
					if (is_char_in_set@Node_regExp(thisnode, peek(tgt_, left_))) {return -1}
					return 1
			swend
		
		//左ノードをもつパターン
			addr_left=get_addr_left@Node_regExp(thisnode) : assertEx (addr_left!=NULL)
			addr_right=get_addr_right@Node_regExp(thisnode)
			
			if (oc==OC_JOIN) {
				assertEx (addr_right!=NULL)
				len_match_left=match_(tgt_, left_, right_, addr_left, capt_info_)
				if (len_match_left==-1) {return -1}
				len_match_right=match_(tgt_, left_+len_match_left, right_, addr_right, capt_info_)
				if (len_match_right==-1) {return -1}
				return len_match_left+len_match_right
			}
			if (oc==OC_OR) {
				assertEx (addr_right!=NULL)
				len_match_left=match_(tgt_, left_, right_, addr_left, capt_info_)
				len_match_right=match_(tgt_, left_, right_, addr_right, capt_info_)
				assertEx ((left_+len_match_left<right_)&&(left_+len_match_right<right_))
				if ((len_match_left==-1)&&(len_match_right==-1)) {return -1}
				if (len_match_left>len_match_right) {return len_match_left}
				return len_match_right
			}
			if (oc==OC_ZERO_OR_ONE) {
				/*
					tgt_="a"
					pattern=".?a"
					
					のような病理的なケースにも対処せなばならぬ
				*/
				len_match_left=limit(match_(tgt_, left_, right_, addr_left, capt_info_), 0)
				assertEx (left_+len_match_left<=right_)
				
				if (addr_right==NULL) {return len_match_left}
				len_match_right=match_(tgt_, left_+len_match_left, right_, addr_right, capt_info_)
				if (len_match_right==-1) {
					len_match_right=match_(tgt_, left_, right_, addr_right, capt_info_)	//左オペランドを無視してもう一度試す
					if (len_match_right>=0) {return len_match_right}
					return -1
				}
				assertEx (left_+len_match_left+len_match_right<=right_)
				return len_match_left+len_match_right
			}
			if ((oc==OC_ZERO_OR_MORE)||(oc==OC_ONE_OR_MORE)) {
				/*
					tgt_="a"
					pattern=".*?a"
					
					のような病理的なケースにも対処せなばならぬ
				*/
				//OC_ZERO_OR_MORE については左オペランド無視で試す
				if (oc==OC_ZERO_OR_MORE) {
					if (addr_right==NULL) {return 0}	//もうそれでいい
					len_match_right=match_(tgt_, left_, right_, addr_right, capt_info_)
					if (len_match_right>=0) {return len_match_right}	//もうそれでいい
				}
				
				left=left_
				repeat
					if (left==right_) {len_match=-1 : break}
					
					len_match_left=match_(tgt_, left, right_, addr_left, capt_info_)
					assertEx (left+len_match_left<=right_)
					
					if (len_match_left>=0) {
						if (addr_right!=NULL) {
							len_match_right=match_(tgt_, left+len_match_left, right_, addr_right, capt_info_)
							assertEx (left+len_match_left+len_match_right<=right_)
							if (len_match_right>=0) {
								len_match=left+len_match_left+len_match_right-left_
								break
							} else {
								left+=limit(len_match_left,1)	//^*?hoge への対処
								continue
							}
						} else {
							len_match=left+len_match_left-left_
							break
						}
					} else {
						if (addr_right!=NULL) {
							len_match=-1
							break
						} else {
							len_match=left-left_
							break
						}
					}
				loop
				return len_match
			}
			if ((oc==OC_ZERO_OR_MORE_GREEDY)||(oc==OC_ONE_OR_MORE_GREEDY)) {
				best_record_left2=-1	//右オペランドがマッチした位置の最高記録
				best_record_len_match_right=-1	//↑における一致の長さ
				
				//OC_ZERO_OR_MORE_GREEDY については左オペランド無視で試す
				if (oc==OC_ZERO_OR_MORE_GREEDY) {
					if (addr_right==NULL) {
						best_record_left2=left_ : best_record_len_match_right=0
					} else {
						len_match_right=match_(tgt_, left_, right_, addr_right, capt_info_)
						if (len_match_right>=0) {
							best_record_left2=left_ : best_record_len_match_right=len_match_right
						}
					}
				}
				
				left=left_
				repeat
					if (left==right_) {break}
					len_match_left=match_(tgt_, left, right_, addr_left, capt_info_)
					assertEx (left+len_match_left<=right_)
					
					if (len_match_left>=0) {
						if (addr_right!=NULL) {
							len_match_right=match_(tgt_, left+len_match_left, right_, addr_right, capt_info_)
							assertEx (left+len_match_left+len_match_right<=right_)
							if (len_match_right>=0) {
								best_record_left2=left+len_match_left
								best_record_len_match_right=len_match_right
							}
							left+=limit(len_match_left,1)	//^*hoge への対処
							continue
						} else {
							best_record_left2=left+len_match_left
							best_record_len_match_right=0
							left+=limit(len_match_left,1)	//^*hoge への対処
							continue
						}
					} else {
						if (addr_right!=NULL) {
							break
						} else {
							best_record_left2=left
							best_record_len_match_right=0
							break
						}
					}
				loop
				if (best_record_left2==-1) {return -1}
				return best_record_left2+best_record_len_match_right-left_
			}
			if ((oc==OC_N)||(oc==OC_N_)||(oc==OC_NM)) {
				//左オペランドの繰り返し回数のチェック
				left=left_
				count_match=0	//マッチした回数
				len_match=0	//マッチした長さの累積
				repeat
					if (left==right_) {break}
					
					len_match_left=match_(tgt_, left, right_, addr_left, capt_info_)
					assertEx (left+len_match_left<=right_)
					
					if (len_match_left>=0) {
						count_match++ : len_match+=len_match_left
						left+=len_match_left
						continue
					} else {break}
				loop
				
				switch oc
					case OC_N : if (count_match!=get_n@Node_regExp(thisnode)) {return -1} : swbreak
					case OC_N_ : if (count_match<get_n@Node_regExp(thisnode)) {return -1} : swbreak
					case OC_NM : if ((count_match<get_n@Node_regExp(thisnode))||(count_match>get_m@Node_regExp(thisnode))) {return -1} : swbreak
					default
						assertEx (FALSE)
				swend
				assertEx (left_+len_match<=right_)
				
				//右オペランドのチェック
				if (addr_right==NULL) {return len_match}
				len_match_right=match_(tgt_, left_+len_match, right_, addr_right, capt_info_)
				if (len_match_right==-1) {return -1}
				assertEx (left_+len_match+len_match_right<=right_)
				
				return len_match+len_match_right
			}
			if (oc==OC_POSITIVE_LOOKAHEAD) {
				len_match_left=match_(tgt_, left_, right_, addr_left, capt_info_)
				assertEx (left_+len_match_left<=right_)
				return limit(len_match_left, -1,0)
			}
			if (oc==OC_NEGATIVE_LOOKAHEAD) {
				len_match_left=match_(tgt_, left_, right_, addr_left, capt_info_)
				assertEx (left_+len_match_left<=right_)
				if (len_match_left==-1) {return 0}
				return -1
			}
			if (oc==OC_CAPTURE) {
				len_match_left=match_(tgt_, left_, right_, addr_left, capt_info_)
				assertEx (left_+len_match_left<=right_)
				if (len_match_left==-1) {return -1}
				add@Capt_info_regExp capt_info_, left_, len_match_left
				return len_match_left
			}
		
		assertEx(FALSE)
		return
	
	#defcfunc regExp_search str tgt_, int left_, int right_, int max_match_, array idx_match_, array length_match_, array capt_info_array_, local tgt, local max_match, local count_match, local left, local len_match, local capt_info	//マッチ判定
		/*
			登録済みのパターンを使って検索
			
			tgt_ : ターゲット文字列
			left_, right_ : 検索開始,終了位置(終了位置は解析対象に含まれない)
			max_match_ : 検索する最大個数。-1を指定すると INT_MAX($7FFFFFFF=214783647) として扱う(事実上無制限になる)。
			idx_match_ : マッチしたインデックスを保存する配列
			length_match_ : マッチした文字列の長さを保存する配列
			capt_info_array_ : キャプチャ情報(Capt_info_regExp モジュール変数)を保存する配列
				idx_match_, length_match_, capt_info_array_ のi番目要素にはi番目にマッチしたものの情報が保存される。
			
			[戻り値]
				(-2, -1, larger) : (パターン未登録, 引数不正, マッチした個数)
			
		*/
		if (tree_exists()==FALSE) {return -2}
		if ((left_<0)||(right_<0)||(left_>right_)) {return -1}
		if (left_==right_) {return 0}
		if (right_>strlen(tgt_)) {return -1}
		if (max_match_<-1) {return -1}
		
		clear_mod_var_array capt_info_array_
		
		tgt=tgt_
		if (max_match_==-1) {max_match=$7FFFFFFF} else {max_match=max_match_}
		left=left_ : count_match=0
		repeat
			if ((left==right_)||(count_match==max_match)) {break}
			
			newmod capt_info_array_, Capt_info_regExp
			len_match=match_(tgt, left, right_, addr_root, capt_info_array_(count_match))
			assertEx (left+len_match<=right_)
			
			if (len_match>=0) {
				idx_match_(count_match)=left : length_match_(count_match)=len_match
				count_match++
				left+=limit(len_match,1)
				continue
			}
			delmod capt_info_array_(count_match)
			if (is_first_byte_of_zenkaku(peek(tgt, left))) {left+=2} else {left++}
		loop
		
		return count_match
	
	#defcfunc regExp_match str tgt_, var capt_info_, local tgt, local len_match	//簡易マッチ
		/*
			tgt_ : ターゲット文字列
			capt_info_ : キャプチャ情報(Capt_info_regExp モジュール変数)を保存
			
			[戻り値]
				(-3,-2,-1,1) : (パターン未登録, 引数不正, マッチしない, マッチした長さ)
		*/
		if (tree_exists()==FALSE) {return -3}
		if (strlen(tgt_)==0) {return -2}
		
		clear_mod_var_array capt_info_
		
		tgt=tgt_
		newmod capt_info_, Capt_info_regExp
		len_match=match_(tgt, 0, strlen(tgt), addr_root, capt_info_)
		assertEx (len_match<=strlen(tgt))
		
		if (len_match>=0) {return len_match}
		return -1
#global

init@mod_regExp

//後片付け
	#undef DEBUGMODE
	#undef assertEx
	
	#undef TRUE
	#undef FALSE
	#undef NULL
	
	#undef VARTYPE_MODULE

	#undef OC_INVALID
	#undef OC_SIMPLE
	#undef OC_ANY_ENG_LET
	#undef OC_NOT_ENG_LET
	#undef OC_ANY_SPACE
	#undef OC_NOT_SPACE
	#undef OC_ANY_DIGIT
	#undef OC_NOT_DIGIT
	#undef OC_ANY
	#undef OC_BOUND
	#undef OC_NOT_BOUND
	#undef OC_LINEHEAD
	#undef OC_LINEEND
	#undef OC_JOIN
	#undef OC_OR
	#undef OC_ZERO_OR_ONE
	#undef OC_ZERO_OR_MORE
	#undef OC_ZERO_OR_MORE_GREEDY
	#undef OC_ONE_OR_MORE
	#undef OC_ONE_OR_MORE_GREEDY
	#undef OC_N
	#undef OC_N_
	#undef OC_NM
	#undef OC_SET
	#undef OC_ANTI_SET
	#undef OC_PACK
	#undef OC_POSITIVE_LOOKAHEAD
	#undef OC_NEGATIVE_LOOKAHEAD
	#undef OC_CAPTURE
	#undef OC_DUMMY