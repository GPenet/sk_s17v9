
//========================================
const char * zh_g_cpt[10] = { "npuz", "guess", "close_d ", "upd1 ", "upd2 ",
"fupd ", "hpair ", "htripl ", " ", " " };

const char * libs_c17_00_cpt2g[100] = {
	"0 bands1+2 processed entries M10",//0
	"1 total bands 3",//1
	"2 new 7_8 ",//2
	"3 3 clues ",	
	"4 6 clues ",	
	"5 after [4] ",
	"6 9 clues",
	"7 set b12 ",
	"8 go b3",
	"9 min ok g2 g3",

	"10 cpt nc128",
	"11 new 4_6 go",

	"12 expand 7",
	"13 cpt uas 7", 
	"14 active new6",
	"15 active exp 7",
	"16 entry expand 8",
	"17 uas expand 8",
	"18 active expand 8 ",

	"19 add guam",
	"20 addg2", 
	"21 addg3",
	"22  build9",
	"23 goa call",
	"24 after goa ",
	"25 gob call ",

	"26  dis5 trouve","27 dis4 trouve ",
	"28 dis3 trouve","29 dis2 trouve",

	"30 check valid2",
	"31 check valid3",
	"32 go subcrit ","33 ","34  ","35 ","36  ",	
	"37  old 7 ",
	"38 old 8", 
	"39 ",
	"40 40 filter  ",
	"41 7-8 cpt gtua8",
	"42 max gtua8",
	"43 max one gtu8",
	"44 ng2_8","45 ng2_9","46 n build9","47 ","48 ","49 ",
	"50 cpt 4","51 cpt 5 ",
	"52 cpt 7","53 cpt 7ok","54 cpt 7nc ",
	"55 crit 7","56 crit7ok ",
	"57 ","58 ","59  ",
	"60 cpt 8","61 cpt 8ok",
	"62 8 crit","63 8 critok",
	"64 8 ncrit","65 ","66 ","67 ","68 ","69 ",
	"70 ","71 ","72 ","73 ","74 ","75 ","76 ","77 ","78 ","79 ",
	"80 cumul ntg2","81 ","82 ","83 ","84 ","85 ","86 ","87 ","88 ","89 ",
	"90 ","91 ","92 ","93 ","94 ","95 ","96 ","97 ","98 ","99 ",

};


void BandReShape(int* s, int* d, BANDMINLEX::PERM p) {
	int * pc = p.cols;
	//uint8_t* pc = p.cols;
	for (int irow = 0; irow < 3; irow++) {
		int drow = 9 * irow;
		for (int icol = 0; icol < 9; icol++)
			d[drow + icol] = p.map[s[drow + pc[icol]]];
	}
	int temp[9];// now reorder 
	if (d[0] > d[9]) {
		memcpy(temp, &d[0], sizeof temp);
		memcpy(&d[0], &d[9], sizeof temp);
		memcpy(&d[9], temp, sizeof temp);
	}
	if (d[0] > d[18]) {
		memcpy(temp, &d[0], sizeof temp);
		memcpy(&d[0], &d[18], sizeof temp);
		memcpy(&d[18], temp, sizeof temp);
	}
	if (d[9] > d[18]) {
		memcpy(temp, &d[9], sizeof temp);
		memcpy(&d[9], &d[18], sizeof temp);
		memcpy(&d[18], temp, sizeof temp);
	}
}
void BandReOrder(int* d) {
	int temp[9];// now reorder 
	if (d[0] > d[9]) {
		memcpy(temp, &d[0], sizeof temp);
		memcpy(&d[0], &d[9], sizeof temp);
		memcpy(&d[9], temp, sizeof temp);
	}
	if (d[0] > d[18]) {
		memcpy(temp, &d[0], sizeof temp);
		memcpy(&d[0], &d[18], sizeof temp);
		memcpy(&d[18], temp, sizeof temp);
	}
	if (d[9] > d[18]) {
		memcpy(temp, &d[9], sizeof temp);
		memcpy(&d[9], &d[18], sizeof temp);
		memcpy(&d[18], temp, sizeof temp);
	}
}
int BandCompare(int* a, int* b) {
	for (int i = 0; i < 27; i++) {
		if (a[i] > b[i]) return 1;
		if (a[i] < b[i]) return -1;
	}
	return 0;

}
void BandDump(int* a, char * lib) {
	for (int i = 0; i < 27; i++) cout << a[i] + 1;
	cout << " " << lib << endl;
}
void GridDump(int* a, char* lib) {
	for (int i = 0; i < 81; i++) cout << a[i] + 1;
	cout << " " << lib << endl;
}
void Table54Dump(uint64_t* tin, uint32_t ntin) {
	for (uint32_t i = 0; i < ntin; i++)
		cout << Char54out(tin[i]) << " " << i 
		<<" "<<__popcnt64(tin[i]) << endl;
}
void Go_c17_00( ) {// p2 process
	cout << "Go_c17_00 search batch 17/18 clues  " << endl;
	op.SetUp(0);
	//return;
	//int it16_start = sgo.vx[0];
	g17b.aigstop=0;
	if (sgo.vx[2] < 0) {
		cerr << "invalid value for skip" << endl;
		return;
	}
	if (sgo.vx[3] < sgo.vx[2]) {
		cerr << "invalid value for last to process" << endl;
		return;
	}
	zh_g.modevalid = 1;
	zh_g2.grid0 = genb12.grid0;
	zh_g2.zsol = zh_g2.stdfirstsol;
	memset(p_cptg, 0, sizeof p_cptg);// used in debugging sequences only
	memset(p_cpt1g, 0, sizeof p_cpt1g);// used in debugging sequences only
	memset(p_cpt2g, 0, sizeof p_cpt2g);// used in debugging sequences only
	genb12.Start(0);
	genb12.NewBand1(op.b1);
	cout << "print final stats" << endl;
	for (int i = 0; i < 100; i++) {
		if (!p_cpt2g[i])continue;
		cout << p_cpt2g[i] << "\t\t" << libs_c17_00_cpt2g[i] << endl;
	}
	cout << "exit final stats" << endl;
}

struct CLBS {// clues band stack
	uint16_t b[3];
	uint16_t s[3];
	inline void Init(uint64_t bf54, uint16_t n) {
		register uint64_t U = bf54;
		b[0] = (uint16_t)_popcnt64(U & BIT_SET_27);
		b[1] = n - b[0];
		b[2] = 0;
		register uint64_t S = stack1_54;
		s[0] = (uint16_t)_popcnt64(U & S);
		S <<= 3;
		s[1] = (uint16_t)_popcnt64(U & S);
		s[2] = n - s[0] - s[1];
	}
	inline void Add(uint32_t cell) {
		b[cell / 27]++;
		s[C_stack[cell]]++;
	}
	
	void Status() {
		cout << " bx " << b[0] << b[1] << b[2]
			<< " sx " << s[0] << s[1] << s[2];

	}
};

void PermBands(char* z163, int* pi1, int* pi2, int i1, int i2) {
	register int ix = *pi1; *pi1 = *pi2; *pi2 = ix;
	char temp[27];
	memcpy(temp, &z163[27 * i1], 27);
	memcpy(&z163[27 * i1], &z163[27 * i2], 27);
	memcpy(&z163[27 * i2], temp, 27);
	memcpy(temp, &z163[27 * i1 + 82], 27);
	memcpy(&z163[27 * i1 + 82], &z163[27 * i2 + 82], 27);
	memcpy(&z163[27 * i2 + 82], temp, 27);
}
void BandReShapewithknown(int* s, char* d, char* sk, char* dk, BANDMINLEX::PERM p) {
	int* pc = p.cols;
	//uint8_t* pc = p.cols;
	for (int irow = 0; irow < 3; irow++) {
		int drow = 9 * irow;
		for (int icol = 0; icol < 9; icol++) {
			int x = p.map[s[drow + pc[icol]]];
			char c = sk[drow + pc[icol]],
				cx = (char)x + '1';
			d[drow + icol] = cx;
			if (c == '.')dk[drow + icol] = '.';
			else dk[drow + icol] = cx;
		}
	}
	char temp[9];// now reorder 
	char tempk[9];
	if (d[0] > d[9]) {
		memcpy(temp, &d[0], 9);
		memcpy(&d[0], &d[9], 9);
		memcpy(&d[9], temp, 9);
		memcpy(tempk, &dk[0], 9);
		memcpy(&dk[0], &dk[9], 9);
		memcpy(&dk[9], tempk, 9);
	}
	if (d[0] > d[18]) {
		memcpy(temp, &d[0], 9);
		memcpy(&d[0], &d[18], 9);
		memcpy(&d[18], temp, 9);
		memcpy(tempk, &dk[0], 9);
		memcpy(&dk[0], &dk[18], 9);
		memcpy(&dk[18], tempk, 9);
	}
	if (d[9] > d[18]) {
		memcpy(temp, &d[9], 9);
		memcpy(&d[9], &d[18], 9);
		memcpy(&d[18], temp, 9);
		memcpy(tempk, &dk[9], 9);
		memcpy(&dk[9], &dk[18], 9);
		memcpy(&dk[18], tempk, 9);
	}
}

struct T12A {
	char* ze, * zke;
	char zs[164], *zks;
	char zsr[164], * zksr;
	int zs0[82], ib1, ib2, ib3, ib1a, ib2a, ib3a,na;
	int  band2min[27], band2minr[27], tmini[108],nmini,
		band3min[27], tmini3[108], nmini3;
	BANDMINLEX::PERM* t_autom;
	void ReshapeZe() {
		zks = &zs[82];
		for (int i = 0; i < 81; i++) zs0[i] = ze[i] - '1';
		BANDMINLEX::PERM perm_ret;
		bandminlex.Getmin(zs0, &perm_ret);
		ib1 = perm_ret.i416;
		//Print("before reshape");
		BandReShapewithknown(zs0, zs, zke, zks, perm_ret);
		BandReShapewithknown(&zs0[27], &zs[27], &zke[27], &zks[27], perm_ret);
		BandReShapewithknown(&zs0[54], &zs[54], &zke[54], &zks[54], perm_ret);
		//cout << zks << " zks reshaped" << endl;
		//cout << &zs[82] << " &zs[82] reshaped" << endl;
		memcpy(ze, zs, 164);
		Print("after reshape");

		for (int i = 0; i < 81; i++) zs0[i] = ze[i] - '1';
	}
	void MorphToPerm(char* z, BANDMINLEX::PERM& p) {
		int z0[81];
		char s[164], * ks=&s[82],*ke=&z[82];	
		s[81] = ';'; ks[81] = 0;
		for (int i = 0; i < 81; i++) z0[i] = z[i] - '1';
		BandReShapewithknown(z0, s, ke, ks, p);
		BandReShapewithknown(&zs0[27], &s[27], &ke[27], &ks[27], p);
		BandReShapewithknown(&zs0[54], &s[54], &ke[54], &ks[54], p);
		memcpy(z, s, 164);

	}


	void Init(char* e) {
		ze = e;		
		zke = &ze[82]; zks = &zs[82];
		zs[81] = ';'; zks[81] = 0;
		BANDMINLEX::PERM perm_ret;
		bandminlex.Getmin(zs0, &perm_ret);
		ib1 = perm_ret.i416; ib1a = t416_to_n6[ib1];
		bandminlex.Getmin(&zs0[27], &perm_ret);
		ib2 = perm_ret.i416; ib2a = t416_to_n6[ib2];
		bandminlex.Getmin(&zs0[54], &perm_ret);
		ib3 = perm_ret.i416; ib3a = t416_to_n6[ib3];
		RigthOrder();
		if (op.ton)Print(" after reorg");	
	}
	void RigthOrder() {
		if (ib2a < ib1a)PermBands(ze, &ib1a, &ib2a, 0, 1);
		if (ib3a < ib1a)PermBands(ze, &ib1a, &ib3a, 0, 2);
		if (ib3a < ib2a)PermBands(ze, &ib2a, &ib3a, 1, 2);
	}
	void Init13(char* e)
	{
		ze = e;
		zke = &ze[82]; zks = &zs[82];
		zs[81] = ';'; zks[81] = 0;
		BANDMINLEX::PERM perm_ret;
		bandminlex.Getmin(zs0, &perm_ret);
		ib1 = perm_ret.i416; ib1a = t416_to_n6[ib1];
		bandminlex.Getmin(&zs0[27], &perm_ret);
		ib2 = perm_ret.i416; ib2a = t416_to_n6[ib2];
		bandminlex.Getmin(&zs0[54], &perm_ret);
		ib3 = perm_ret.i416; ib3a = t416_to_n6[ib3];
	}
	void Print(const char* lib) {
		cout << ze << ";\t" << ib1a << ";" << ib2a << ";" << ib3a << lib << endl;
	}
	void Print2(const char* lib) {
		char zw[164];
		memcpy(zw, ze, 164); zw[81] = 0;
		cout << zw << endl;
		cout << &zw[82] << ";" << ib1a << ";" << ib2a << ";" << ib3a << lib
			<< " na=" << na;
		if (na) cout << " nmin1=" << nmini;
		cout << endl;
	}
	void PrintCFX(const char* lib) { cout << zs << lib << endl; }
	void GetCFX() {
		zke = &ze[82]; zks = &zs[82];
		zs[81] = ';'; zks[81] = 0;
		ReshapeZe();
		if (op.ton)Print("ze reshaped 2eme");


		na = tblnauto[ib1]; //ia 0-415 not index
		if (!na) { GetCFX_NoAuto();  return; }
		if (op.ton)cout << "work with morhs na=" << na << endl;;
		t_autom = &automorphsp[tblnautostart[ib1]];
		GetSmaller();
		if (op.ton)cout << "back nmini= " << nmini << endl;;
		if (ib2a == ib3a) {
			GetSmaller3();
			int ir = G17ComparedOrderedBand(band2min, band3min);
			if (op.ton)cout << "back smaller3 ir= " << ir << endl;;
			if (ir == 1) {
				PermBands(ze, &ib2a, &ib3a, 1, 2);
				for (int i = 0; i < 81; i++) zs0[i] = ze[i] - '1';
				GetSmaller();// redo it after perm
				if (op.ton) {
					for (int i = 0; i < 27; i++) cout << band2min[i] + 1;
					cout << "  new back after perm b2 b3 nmini= " << nmini << endl;
					Print("new ze after perm");

				}
			}
			else if (!ir) { 
				return; // do nothing, seems neutral with known
				Print("same mini band2 band3"); 
				memcpy(zsr, zs, 164);// save 
				MorphToPerm(zsr, t_autom[tmini[0]]);
				PermBands(zs, &ib2a, &ib3a, 1, 2);
				MorphToPerm(zs, t_autom[nmini3]);
				cout << zsr << " old morphed"<<endl;
				cout << zs << " new morphed"<<endl;
				//must take mini b3 on perm giving band2/3 min
				return; 
			}// small window for case ==
		}
		
		if (nmini == 1) { // work on morph
			int ia = tmini[0];
			if (ia >= 0) {
				BANDMINLEX::PERM perm_ret = t_autom[tmini[0]];
				BandReShapewithknown(zs0, zs, zke, zks, perm_ret);
				BandReShapewithknown(&zs0[27], &zs[27], &zke[27], &zks[27], perm_ret);
				BandReShapewithknown(&zs0[54], &zs[54], &zke[54], &zks[54], perm_ret);

			}
			if (ib1a != ib2a) { 
				if (op.ton) {
					cout << "call no auto then end" << endl;
					Print("at call");
				}
				//GetCFX_NoAuto(); 
				return; }
			if (op.ton)cout << "must see perm b1 b2" << endl;
			memcpy(zsr, zs, 164);// save 
			memcpy(band2minr, band2min, sizeof band2minr);
			PermBands(ze, &ib1a, &ib2a, 0, 1);
			ReshapeZe();
			if (op.ton)Print("reshaped  zw after perm b1b2");
			GetSmaller();
			if (op.ton) {
				for (int i = 0; i < 27; i++) cout << band2min[i] + 1;
				cout << " min nmini after perm=" << nmini << endl;

			}
			for (int i = 0; i < 81; i++) {// take smaller
				if (zsr[i] > zs[i])break;
				if (zsr[i] < zs[i]) {
					memcpy(zs, zsr, 164);
					return;
				}
			}
			return; // use after perm
		}
		if ((ib1a == ib2a) || (ib3a == ib2a)) {
			// must ckeck b3 min
			cout << nmini << " "; Print("nmini>1");
		}

	}
	void GetCFX13() {
		na = tblnauto[ib1]; //ia 0-415 not index
		if (!na)   return; 
		t_autom = &automorphsp[tblnautostart[ib1]];
		GetSmaller();
		for (int i = 0; i < 27; i++) cout << band2min[i] + 1;
		cout << " min nmini=" << nmini << endl;
		if (nmini == 1) { // work on morph
			BANDMINLEX::PERM perm_ret = t_autom[tmini[0]];
			BandReShapewithknown(zs0, zs, zke, zks, perm_ret);
			BandReShapewithknown(&zs0[27], &zs[27], &zke[27], &zks[27], perm_ret);
			BandReShapewithknown(&zs0[54], &zs[54], &zke[54], &zks[54], perm_ret);
			cout<<zs<<endl <<zks<< " after new min="  << endl;
		}

	}

	void GetSmaller() {
		nmini = 1; tmini[0] = -1;
		memcpy(band2min, &zs0[27], sizeof band2min);
		for (int imorph = 0; imorph < na; imorph++) {
			int* z = &zs0[27];// morph the band
			BANDMINLEX::PERM p = t_autom[imorph]; SKT_MORPHTOP
				int ir = G17ComparedOrderedBand(band2min, band);
			if (ir > 1) continue;
			if (!ir) { tmini[nmini++] = imorph;		continue; }
			// now a lower
			nmini = 0;
			tmini[nmini++] = imorph;
			BandReOrder(band);
			memcpy(band2min, band, sizeof band2min);
		}
	}
	void GetSmaller3() {
		nmini3 = 1; tmini3[0] = -1;
		memcpy(band3min, &zs0[54], sizeof band3min);
		for (int imorph = 0; imorph < na; imorph++) {
			int* z = &zs0[54];// morph the band
			BANDMINLEX::PERM p = t_autom[imorph]; SKT_MORPHTOP
				int ir = G17ComparedOrderedBand(band3min, band);
			if (ir > 1) continue;
			if (!ir) { tmini3[nmini3++] = imorph;		continue; }
			// now a lower
			nmini3 = 0;
			tmini3[nmini3++] = imorph;
			BandReOrder(band);
			memcpy(band3min, band, sizeof band3min);
		}
	}

	void GetCFX_NoAuto() {
		if (ib1a != ib2a && ib2a != ib3a) return; // nothing to do
		// redo zs0 from zs
		for (int i = 0; i < 81; i++) zs0[i] = zs[i] - '1';
		BANDMINLEX::PERM p;
		if (ib1a == ib2a) {// try reverse b1b2
			bandminlex.Getmin(&zs0[27], &p, 0);
			// morph b1 to b2 see if lower
			int ir, ir2;
			{
				int* z = zs0;// morph the band
				SKT_MORPHTOP
					ir = G17ComparedOrderedBand(&zs0[27], band);
			}
			if (ir < 0) return;// source was lower 
			if (!ir) {// automorph b1b2 see b3 
				int* z = &zs0[54]; SKT_MORPHTOP
					ir2 = G17ComparedOrderedBand(&zs0[54], band);
				if (ir2 <= 0) return;
			}
			if (op.ton)cout << "perm b1 b2 to do" << endl;
			memcpy(ze, zs, 164);
			PermBands(ze, &ib1a, &ib2a, 0, 1);
			ReshapeZe();
			return;
		}
		if (ib3a == ib2a) {// reverse b2b3 if not right order
			if (zs[27] < zs[54]) return;
			if (op.ton)cout << "perm b2 b3 to do" << endl;
			memcpy(ze, zs, 164);
			PermBands(ze, &ib2a, &ib3a, 1, 2);
			ReshapeZe();
		}
	}

};
struct T12 {
	T12A zw, zwd;
	char zed[164]; 
	int mode;
	void Init(char* ze) {
		zed[81] = ';';
		zed[163] = 0;
		for (int i = 0; i < 81; i++) {
			register int id = C_transpose_d[i];
			zed[i] = ze[id];
			zed[82 + i] = ze[id + 82];
			zw.zs0[i] = ze[i] - '1';
			zwd.zs0[i] = ze[id] - '1';
		}
		zw.Init(ze); zwd.Init(zed);
	}
	void SetMode() {
		mode =0;
		if (zwd.ib1a > zw.ib1a) return;
		if (zwd.ib1a < zw.ib1a) { mode = 1; return; }
		if (zwd.ib2a > zw.ib2a) return;
		if (zwd.ib2a < zw.ib2a) { mode = 1; return; }
		if (zwd.ib3a < zw.ib3a) { mode = 1; }

	}
	void Init13(char* ze) {
		for (int i = 0; i < 81; i++) 			zw.zs0[i] = ze[i] - '1';
		zw.Init13(ze); 
	}

};

void Go_c17_12() {// process 17 file to get CFX mode
	// search 17 using a file having known  as entry and one 17 given 6 6 5
	char* ze = finput.ze;
	uint64_t npuz = 0;
	op.ton = sgo.vx[0];
	op.known = sgo.vx[5]; // no known if 1
	cout << "Go_c17_12() band analysis build min bx mode vx[5]" 
		<<op.known  <<" op.ton="<< op.ton << endl;
	while (finput.GetLigne()) {
		if (op.known) {// must add it for this process
			if (strlen(ze) < 81)continue;
			memcpy(&ze[82], ze, 81);// all is known
			ze[163] = 0;
		}
		if (strlen(ze) < 163)continue;
		if (npuz++ <sgo.vx[1])continue;
		if(op.ton>1)cout << ze << endl;
		T12 zt12;
		zt12.Init(ze); zt12.SetMode();
		if (zt12.mode) {
			if (op.ton)cout << " use diag " << endl;
			zt12.zw = zt12.zwd;
		}
		if ( op.ton)zt12.zw.Print("start zw");
		zt12.zw.ReshapeZe();

		if (op.ton)zt12.zw.Print("ze reshaped");

		zt12.zw.GetCFX();
		int nclb[3] = { 0,0,0 };
		for (int ib = 0,i=0; ib < 3; ib++) {
			for (int j = 0; j < 27; j++, i++) {
				if (zt12.zw.zks[i] != '.')nclb[ib]++;
			}
		}
		zt12.zw.zs[81] = 0;
		fout1 << &zt12.zw.zs[82]<<";"
			<< zt12.zw.zs << ";"		
			<< zt12.zw.ib1a << ";"	<< zt12.zw.ib2a << ";"	<< zt12.zw.ib3a 
			<< ";"	<< nclb[0] << ";" << nclb[1] << ";" << nclb[2] << endl;

		if (op.ton > 1) {
			if (zt12.zw.na || (zt12.zw.ib1a == zt12.zw.ib2a) || (zt12.zw.ib2a == zt12.zw.ib3a))
				zt12.zw.Print2(" end ze");
		}
		if (npuz >= sgo.vx[2])return;;
	}
}


void Go_c17_13() {// process 17 file to get CFX mode for p1 file
	// search 17 using a file having known  as entry and one 17 given 6 6 5
	char* ze = finput.ze;
	uint64_t npuz = 0;
	cout << "Go_c17_13() band analysis get expected NEDx file"   << endl;
	op.known = sgo.vx[5]; // no known if 1
	while (finput.GetLigne()) {
		if (op.known) {// must add it for this process
			if (strlen(ze) < 81)continue;
			memcpy(&ze[82], ze, 81);// all is known
			ze[163] = 0;
		}	
		if (strlen(ze) < 163)continue;
		if (npuz++ < sgo.vx[1])continue;
		if (op.ton) cout << ze << endl;
		T12 zt12;
		zt12.Init13(ze);  
		if (op.ton)zt12.zw.Print("start zw");
		zt12.zw.ReshapeZe();
		if (op.ton)zt12.zw.Print("ze reshaped");
		zt12.zw.GetCFX13();
		//if (zt12.zw.ib3a == zt12.zw.ib2a)zt12.zw.PrintCFX("start zw cfx");
		if (npuz >= sgo.vx[2])return;;
	}
}

void Go_c17_10() {// check on known
	char* ze = finput.ze;
	uint32_t npuz = 0;
	cout << "Go_c17_09() check on known using file for 79 " << endl;
	cout << sgo.vx[4] << " -v4- 0 mode p2a 1 mode p2b 2 mode p1" << endl;
	memset(p_cpt2g, 0, sizeof p_cpt2g);// used in debugging sequences only
	op.SetUp(10,'k',1);
	op.ton = sgo.vx[2];
	op.test_ned = 63;
	int x = (int)sgo.vx[4];
	if (x == 2) op.p1 = 1;
	else { op.p2 = 1; if (x == 1) op.p2b = 1; }
	zh_g.modevalid = 1;
	zh_g2.grid0 = genb12.grid0;
	zh_g2.zsol = zh_g2.stdfirstsol;
	int* zs0 = genb12.grid0;
	char* zb = ze + 100;// soution grid location
	while (finput.GetLigne()) {
		if (npuz++ < sgo.vx[0])continue;
		int ll = (int)strlen(ze);
		if (ll != 181) {
			cout << "ligne longueur " << ll << endl;
			continue;
		}
		cout << ze << " in test " << npuz << endl;
		char* items[50];
		int nitems = 1; items[0] = ze;
		for (int i = 81; i < ll; i++) {
			if (!ze[i]) break;
			if (ze[i] == ';') {
				items[nitems++] = &ze[i + 1];
				ze[i] = 0;
			}
			if (nitems >= 9) break;
		}
		if (nitems < 6) continue;
		if (items[5] != zb) {
			cout << " zb " << (uint64_t)zb << " item " << (uint64_t)items[5] << endl;
			continue;
		}

		for (int i = 0; i < 81; i++) zs0[i] = zb[i] - '1';
		genb12.nb12 = 0;
		g17b.npuz = npuz;
		g17b.a_17_found_here = 0;
		g17b.aigstop = 0;

		BANDMINLEX::PERM perm_ret;
		bandminlex.Getmin(zs0, &perm_ret);
		int ib1 = perm_ret.i416, ib1a = t416_to_n6[ib1];
		myband1.InitBand2_3(ib1, zb, perm_ret, 0);
		bandminlex.Getmin(&zs0[27], &perm_ret);
		int ib2 = perm_ret.i416, ib2a = t416_to_n6[ib2];
		myband2.InitBand2_3(ib2, &zb[27], perm_ret, 1);
		bandminlex.Getmin(&zs0[54], &perm_ret);
		int ib3 = perm_ret.i416, ib3a = t416_to_n6[ib3];
		genb12.bands3[0].InitBand3(ib3, &zb[54], perm_ret);
		genb12.nband3 = 1;
		genb12.i1t16 = ib1a;
		genb12.i2t16 = ib2a;

		g17b.p17diag.SetAll_0();
		for (int i = 0; i < 81; i++) if (ze[i] != '.')
			g17b.p17diag.Set_c(i);
		register uint64_t U = g17b.p17diag.bf.u64[0];
		g17b.pk54 = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);
		g17b.pk54n = ~g17b.pk54;
		genb12.ValidInitGang();
		g17b.Start();
		if (!g17b.a_17_found_here) {
			cout << "puz=" << npuz << " failed to find the searched 17" << endl;
			cerr << "puz=" << npuz << " failed to find the searched 17" << endl;
			break;
		}
		if (npuz > sgo.vx[1])return;;
	}
}

/*

//========================= known s17 file 10/19
void Go_c17_10() {

	int* zs0 = genb12.grid0, npuz = 0;
	char* ze2 = &ze[82];

	while (finput.GetLigne()) {
		if (strlen(ze) < 160) continue;// skip blank lines
		npuz++;
		g17b.p17diag.SetAll_0();
		for (int i = 0; i < 81; i++) if (ze[i] != '.') 
			g17b.p17diag.Set_c(i);

		

		ze[81] = 0;
		if (op.ton)
			cout << Char2Xout(g17b.p17diag.bf.u64[0]) << " b12 pattern for the 17" << endl;
		register uint64_t U = g17b.p17diag.bf.u64[0];
		g17b.pk54 = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);
		genb12.ValidInitGang();
		g17b.npuz = npuz;
		if (sgo.bfx[2] & 1)g17b.StartKnown();
		else	g17b.Start();
		//g17b.a_17_found_here = 1;
		if (!g17b.a_17_found_here) {
			cout << "puz=" << npuz << " failed to find the searched 17" << endl;
			cerr << "puz=" << npuz << " failed to find the searched 17" << endl;
			break;
		}
	}
	cout << "print final stats" << endl;
	for (int i = 0; i < 100; i++) {
		if (!p_cpt2g[i])continue;
		cout << p_cpt2g[i] << "\t\t" << libs_c17_00_cpt2g[i] << endl;
	}
}
*/




void Go_c17_79() {// check fully known
	char* ze = finput.ze;
	uint64_t npuz = 0;
	cout << "Go_c17_79() redo 3xbx + slice " << endl;
	cout << sgo.vx[4] << " -v4- 0 mode p2a 1 mode p2b 2 mode p1" << endl;
	memset(p_cpt2g, 0, sizeof p_cpt2g);// used in debugging sequences only
	op.SetUp79();
	op.ton = sgo.vx[2];
	op.test_ned = 63;
	int x = (int)sgo.vx[4];
	if (x == 2) op.p1 = 1;
	else {	op.p2 = 1; if (x == 1) op.p2b = 1;	}
	genb12.Start(0);
	while (finput.GetLigne()) {
		if (npuz++ < sgo.vx[0])continue;
		char  * items[50];
		int nitems = 1; items[0] = ze;
		int ll = (int)strlen(ze);
		for (int i = 81; i < ll; i++) {
			if (!ze[i]) break;
			if (ze[i] == ';') {
				items[nitems++] = &ze[i + 1];
				ze[i] = 0;
			}
			if (nitems >= 9) break;
		}
		if (nitems < 4) continue;
		int bx1= atoi(items[1]), bx2 = atoi(items[2]), bx3 = atoi(items[3]);
		cout << bx1 << " " << bx2 << " " << bx3 << endl;
		if (bx1 > bx2) continue;		if (bx2 > 415) continue;
		if (bx3 > 415) continue;
		if (bx1 < 0 || bx2 < 0 || bx3 < 0) continue;
		int slice = -1;
		if(nitems==5)slice= atoi(items[4]);
		cout << bx1 << " " << bx2 << " " << bx3 <<" "<<slice << endl;
		op.first = 0;
		op.last = 200000;
		if(slice>=0)op.first = 	op.last = slice;
		op.b2 = bx2;		op.bx3 = bx3;
		memset(p_cpt, 0, sizeof p_cpt);// band2 and band 3 count
		genb12.nb12= 0;
		g17b.aigstop = 0;
		genb12.NewBand1(bx1);
		if (npuz > sgo.vx[1])return;;
	}
}
/*
 bande 416 est 134 bx
*/
void Go_c17_80() {// enumeration test
	//return; // revise command line
	cout << "Go_c17_80 phase 2a enumeration test " << endl;
	cout << sgo.vx[0] << " -v0- first id 0_415" << endl;
	cout << sgo.vx[1] << " -v1- second id 0_415" << endl;
	cout << sgo.vx[2] << " -v2- if 1 printout asked" << endl;
	cout << sgo.vx[4] << " -v4- 0 mode p2a 1 mode p2b 2 mode p1" << endl;
	cout << sgo.vx[5] << " -v5- band 2 index if not 9990" << endl;
	cout << sgo.vx[11] << " -vx- band 3 index if not 999" << endl;
	int it16_start = sgo.vx[0], it16_end = sgo.vx[1];
	memset(&op, 0, sizeof op);
	op.first = 0;
	op.last = 200000;
	op.t18 = 0;
	op.ton = sgo.vx[2];
	op.b2 = sgo.vx[5];
	op.bx3 = sgo.vx[11];
	op.out_entry = op.ton;
	op.test_ned = sgo.bfx[5];
	if (!op.test_ned)op.test_ned = 63;// take all good in NED
	cout << op.test_ned << "  option de test pout entr�e" << endl;

	int x = (int)sgo.vx[4];
	if (x == 3) { op.p2min = 1; op.p2 = 1;	}
	if (x == 2) op.p1 = 1;
	else {	op.p2 = 1; if (x == 1) op.p2b = 1;	}
	if (it16_start > 415 || it16_end > 415 || it16_start > it16_end) {
		cerr << "invalid it16_start it16_end" << endl;
		return;
	}
	memset(p_cptg, 0, sizeof p_cptg);// used in debugging sequences only

	genb12.Start(11);// mode p2a or p2b or p1
	for (int i1t16 = it16_start; i1t16 <= it16_end; i1t16++) {
		memset(p_cpt, 0, sizeof p_cpt);// band2 and band 3 count
		genb12.nb12 = 0;
		genb12.NewBand1(i1t16);
		cout <<"endbx " << genb12.i1t16 << "\t" << genb12.it16 << "\t" << p_cpt[0]
			<< "\t" << p_cpt[1] << endl;
		p_cptg[0] += p_cpt[0];
		p_cptg[1] += p_cpt[1];
	}
	cout << "total\t\t" << p_cptg[0]
		<< "\t" << p_cptg[1] << "\t" << p_cpt2g[10] << "\t" << p_cpt2g[11]
		<< "\t" << p_cpt2g[12] << "\t" << p_cpt2g[13]
		<< "\t" << p_cpt2g[14] << "\t" << p_cpt2g[15]
		<< " max nsgcheck " << p_cpt2g[20] << endl;
}
