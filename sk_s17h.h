#define stack1_54 07007007007007007
struct OPCOMMAND {// decoding command line option for this rpocess
	// processing options 
	int opcode;
	int tbn, bx3;// 
	int t18, p1, p2, p2b,//17 of 18 clues, pass or 2 (2a or 2b)
		p2min,
		b2slice, // runing a slice of bands 2 in 18 mode bfx[0] & 8
		b3low, // running band 1 pass1 for slices in pass2 bfx[0] & 16
		out_one,// limit output to one per band 3 .bfx[2] & 1
		out_entry, //output of the entry file for test DLL .bfx[2] & 2
		known; // 1 if known process 2 if known filter active .bfx[2] & 4
	// bfx[2] & 8 special use b2_is as limit b3
	int b1;//band 1 in process 
	int b2, b2_is;//bands b2  forced
	char* b2start;
	int first, last;
	int ton;//test on and test level
	uint64_t f0, f3, f4, f7, f10; // filters p_cpt2g [3] [4) [7]
	int upto3, upto4; // active below f3 below f4
	int dv12, dv3;// print fresh uas bands 1 2 band 3
	int dumpa;
	int test_ned;
	void SetUp(int opcod, int k = 0, int print = 1) {// init known or not
		memset(this, 0, sizeof * this);
		opcode = opcod;
		known = k;
		test_ned = sgo.bfx[5];
		if (!test_ned )test_ned = 63;// take all good in NED
		tbn = sgo.vx[10];
		bx3 = sgo.vx[11];
		f0 = sgo.vx[12];
		if (sgo.bfx[0] & 1)t18 = 1;
		if (sgo.bfx[0] & 6) {// pass 1 2a 2b
			p2 = 1;
			if (sgo.bfx[0] & 4) p2b = 1;
			if (p2b && t18) { p2b = 0; }
		}
		else p1 = 1;
		if (t18 && (sgo.bfx[0] & 8)) {// slice of bands 
			b2slice = 1;
		}
		if (p1 && (sgo.bfx[0] & 16))b3low = 1;

		b1 = sgo.vx[0];
		first = sgo.vx[2];
		last = sgo.vx[3];
		if (last == 0) if (last == 0) { last = first; sgo.vx[3] = first; }  // default if no -v3- given
		b2_is = sgo.vx[4];
		b2 = sgo.vx[5];
		if (sgo.s_strings[0])	if (strlen(sgo.s_strings[0]))
			b2start = sgo.s_strings[0];
		ton = sgo.vx[1];

		f3 = sgo.vx[6];	f4 = sgo.vx[7];
		f7 = sgo.vx[8]; f10 = sgo.vx[9];

		if (sgo.bfx[1] & 1)upto3 = 1;
		if (sgo.bfx[1] & 2)upto4 = 1;
		if (sgo.bfx[1] & 4)dv12 = 1;
		if (sgo.bfx[1] & 8)dumpa = 1;
		if (sgo.bfx[1] & 16)dv3 = 1;

		if (sgo.bfx[2] & 1) out_one = 1;
		if (sgo.bfx[2] & 2) out_entry = 1;
		if(out_entry && ton==5)out_entry = -1;
		if (known)if (sgo.bfx[2] & 4) known = 2;
		if (print) {
			cout << Char9out(sgo.bfx[0]) << " sgo.bfx[0 " << endl;
			cout << "standard processing commands_______________" << endl;
			if (t18) cout << "\t\tsearch 18 clues via -b0-x." << endl;
			else cout << "\t\tsearch 17 clues via -b0-x." << endl;
			if (p1)cout << "\t\tpass1 via -b0-.x." << endl;
			if (p2)cout << "\t\tpass2 via -b0-.x." << endl;
			if (p2b)cout << "\t\tpass2b via -b0-..x." << endl;
			cout << sgo.vx[0] << " b1  -v0- band 0_415" << endl;
			cout << sgo.vx[2] << " first  -v2- first slice to process" << endl;
			cout << sgo.vx[3] << " last  -v3- last slice to process must be >= vx[2]" << endl;
			if (b2slice) {
				cout << "running a slice of bands 2 index from="
					<< b2_is << " to=" << b2 << endl;
			}
			if (b3low)
				cout << " pass1 with limit in band 3 index <= band1 index " << endl;
			if (out_one) cout << " max one out per band 3 sgo.bfx[2] & 1 " << endl;
			if (out_entry)  cout << " file1 contains attached solution grids" << endl;
			cout << "debugging commands___________________" << endl;
			if (known) {
				cout << "processing solution grids with known" << endl;
				if (known > 1)cout << "\tfilter on path active  sgo.bfx[2] & 2" << endl;
			}
			if (b2)		cout << b2 << " b2 -v5- filter band 2 index" << endl;
			if (bx3 < 416)		cout << bx3 << " b3 index" << endl;
			if (b2start)	cout << b2start << " filter band 2 start" << endl;

			if (ton)cout << ton << "  test on  -v1- verbose mode " << endl;
			if (f0)cout << f0 << "  f0  -vz- diag skip pairs b1b2" << endl;
			if (f3)cout << f3 << "  f3  -v6- diag filter 3 clues [3]" << endl;
			if (f4)cout << f4 << "  f4  -v7- diag filter 6 clues [6]" << endl;
			if (f7)cout << f7 << "  f7  -v8- diag filter go full [7]" << endl;
			if (dv12)cout << "  -b1-..x  dump add in valid b12" << endl;
			if (dumpa)cout << "  -b1-...x  dump uas b12 at the start" << endl;
			if (upto3)cout << "upto debugging [3]  sgo.bfx[1] & 1 " << endl;
			if (upto4)cout << "upto debugging [4]  sgo.bfx[1] & 2 " << endl;
			if (dv3)cout << " -b1-...x print fresh adds " << endl;
			cout << test_ned << "  option de test pout entr�e" << endl;
		}
	}
	void SetUp79() {// init 
		memset(this, 0, sizeof * this);
		opcode = 0;
	}
}op;
#define UACNBLOCS 15
//___ expand uas in bands 1+2
struct SPB03A {// spots 6 first clues
	BF128 v;	
	uint64_t  possible_cells, all_previous_cells, active_cells;
};
struct SPB03B {// spots 6 first clues
	BF128 v[UACNBLOCS];
	uint64_t  possible_cells, all_previous_cells, active_cells;
};
// expand uas in band 3
struct SP3 {
	uint32_t  possible_cells, all_previous, active,
		indtw3;
};

//___ permanent data for guas2 guas3
struct SGUA2 {// 81 possible UA2 sockets
	// permanent data
	//uint64_t* tua;
	int col1, col2;// columns of the socket
	int i_81; // index 0_80 for this 
	int i9;// complementary column in minirow
	int id1, id2; // index of digits in gang 27 
	// Current band1+2 data
	int digs, dig1, dig2;// depending on gang27 status
	int valid, // valid if guas 
		validuas,// gua2s found
		used;// if needed in bands3
	int gangcols[9];// revised gangster
	//uint32_t nua;// nua_start, nua_end;

}tsgua2[81];
struct SGUA3 {// 81 possible UA3 sockets
	// permanent data
	//uint64_t* tua;// , killer;
	int col1;// first columns 0-9 
	int i_81, stack;// , iguan; // index 0_80 for this 
	int id1, id2, id3; // index of digits in gang 27 
	// Current band1+2 data
	int  dig1, dig2, dig3, digs;// depending on gang27 status
	int valid, // valid if guas 
		validuas,// gua2s found
		used;// if needed in bands3
	//uint32_t nua;// nua_start, nua_end, nua;
}tsgua3[81];


#define UA12SIZE 3840
#define UA12BLOCS 30
#define GTULSIZE 2000

//_____ uas bands 1+2
struct TUASB12 {//  initial set of uas bands 1+2 
	uint64_t tua[UA12SIZE]; // 30x128
	uint32_t nua,  tdigs[UA12SIZE],ndigs[UA12SIZE];
	inline void AddInit(
		int64_t ua, uint32_t digs,  uint32_t nd) {
		tdigs[nua] = digs;
		ndigs[nua] = nd;
		tua[nua++] = ua;
	}
	void DumpInit() {
		cout << "dumpinit  tua nua=" << nua << endl;
		for (uint32_t iua = 0; iua < nua; iua++) {
			cout << Char2Xout(tua[iua]) << " i="
				<< iua << " " << (tua[iua] >> 59)
				<< " " <<_popcnt64(tua[iua] & BIT_SET_2X);
			cout << " digs " << Char9out(tdigs[iua]) << " " << ndigs[iua] << endl;;
		}
	}
	void DumpShort(const char * lib) {
		cout << lib  << "tuasb12 tua nua=" << nua << endl;
	}

}tuasb12;
struct T54B12 {//   uas bandshttps://www.msn.com/fr-fr/feed 1+2 in 54 mode
	struct TUVECT {//  128 uas and vectors
		BF128 v0, vc[54];
		uint64_t t[128];
		void Init() {
			v0.SetAll_0();
			memset(vc, 255, sizeof vc);
		}
		inline void DoAnd(BF128 v, uint64_t & wa) {
			int ir;
			while ((ir = v.getFirst128()) >= 0) {
				v.clearBit(ir);
				wa &= t[ir];
			}
		}
		void Dumpv(int lim = 32) {
			cout << Char32out(v0.bf.u32[0]) << " v0" << endl;
			for (int i = 0; i < 54; i++)
				cout << Char32out(vc[i].bf.u32[0]) << " cell=" << i << endl;
		}
		void Dump(int lim = 128) {
			for (int i = 0; i < lim; i++)
				if (v0.On(i))
					cout << Char54out(t[i]) << " " << i <<" "<<_popcnt64(t[i]) << endl;
				else return;
		}
	};
	// working area for "build"
	uint64_t tw[UA12SIZE]; // to check redundancy
	BF128 vsize[25][UA12BLOCS];
	BF128 tvw[UA12BLOCS];
	// initial status after harvest plus fresh uas B12
	TUVECT ta128[UA12BLOCS];// max start 20*128=2560 uas 
	uint32_t na128, nablocs, nta128[UA12BLOCS];
	void InitA() {
		memset(nta128, 0, sizeof nta128);
		na128 = nablocs = 0;
		for (int i = 0; i < UA12BLOCS; i++)ta128[i].Init();
	}
inline void AddA(uint64_t u) {
		if (na128 >= UA12BLOCS * 128) return;
		register uint32_t bloc = na128 >> 7, ir = na128 - (bloc << 7);
		na128++; nablocs = bloc; nta128[bloc]++;
		ta128[bloc].v0.setBit(ir);
		BF128* myvc = ta128[bloc].vc;
		register uint64_t R = u;
		ta128[bloc].t[ir] = R;
		R &= BIT_SET_54;// clear extra bits
		uint32_t cell;
		while (bitscanforward64(cell, R)) {
			R ^= (uint64_t)1 << cell; //clear bit
			myvc[cell].clearBit(ir);
		}
	}
	void Build_ta128(uint64_t* t, uint32_t n);

#define UABNBLOCS 20
	// status after 3 clues (B)
	TUVECT tb128[UABNBLOCS];// max start 10*128=1280 uas 
	uint32_t nb128, nbblocs, ntb128[UABNBLOCS];
	void InitB() {
		memset(ntb128, 0, sizeof ntb128);
		nb128 = nbblocs = 0;
		for (int i = 0; i < UABNBLOCS; i++)tb128[i].Init();
	}
	inline void AddB(uint64_t u) {
		if (nb128 >= UABNBLOCS*128) return;
		register uint32_t bloc = nb128 >> 7,
			ir = nb128 - 128 * bloc;
		nb128++; nbblocs = bloc; ntb128[bloc]++;
		tb128[bloc].v0.setBit(ir);
		BF128* myvc = tb128[bloc].vc;
		register uint64_t R = u;
		tb128[bloc].t[ir] = R;
		register uint32_t cell;
		while (bitscanforward64(cell, R)) {
			R ^= (uint64_t)1 << cell; //clear bit
			myvc[cell].clearBit(ir);
		}
	}
	int Build_tb128N();
//   #define UACNBLOCS 15 see befor SPB 
	// status after 6 clues (C)
	TUVECT tc128[UACNBLOCS];// max start 10*128=1280 uas 
	uint64_t tandc;
	uint32_t nc128, ncblocs, ntc128[UACNBLOCS];
	void InitC() {
		memset(ntc128, 0, sizeof ntc128);
		nc128 = ncblocs = 0;
		for (int i = 0; i < UACNBLOCS; i++)tc128[i].Init();
		tandc = ~0;
	}
	inline void AddC(uint64_t u) {
		if (nc128 >= UACNBLOCS * 128) return;
		register uint32_t bloc = nc128 >> 7,
			ir = nc128 - 128 * bloc;
		nc128++; ncblocs = bloc; ntc128[bloc]++;
		tc128[bloc].v0.setBit(ir);
		BF128* myvc = tc128[bloc].vc;
		register uint64_t R = u;
		tc128[bloc].t[ir] = R;
		tandc &= R;
		register uint32_t cell;
		while (bitscanforward64(cell, R)) {
			R ^= (uint64_t)1 << cell; //clear bit
			myvc[cell].clearBit(ir);
		}
	}
	int Build_tc128N();// after 6 clues
	inline int IsNotRedundant(uint64_t u) {
		register uint64_t nu = ~u;
		for (uint32_t i = 0; i < ntc128[0]; i++)
			if (!(tc128[0].t[i] & nu)) return 0;
		return 1;
	}
	inline void AddVect7(uint32_t cell,BF128 * v7) {
		for (uint32_t i = 0; i <= ncblocs; i++)
			v7[i]= tc128[i].vc[cell];
	}
	inline void AddVect(uint32_t cell, BF128* vold, BF128* vnew) {
		for (uint32_t i = 0; i <= ncblocs; i++)
			vnew[i] = tc128[i].vc[cell]&vold[i];
	}


	void DebugA() {
		cout << " debugA na128=" << na128<<" nablocs=" <<nablocs<< endl;
		for (uint32_t i = 0; i <= nablocs; i++) {
			cout << "+ " << 128 * i<< " count " <<nta128[i]  << endl;
			ta128[i].Dump();
		}
	}

	void DebugB() {
		cout << " debugB nb128=" << nb128 << " nbblocs=" << nbblocs << endl;
		for (uint32_t i = 0; i <= nbblocs; i++) {
			cout << "+ " << 128 * i << endl;
			tb128[i].Dump();
		}
	}
	void DebugC() {
		cout << " debugC nc128=" << nc128 << endl;
		for (uint32_t i = 0; i <= ncblocs; i++) {
			cout << "+ " << 128 * i << endl;
			tc128[i].Dump();
		}
	}


}t54b12;

//____ guas (uas with band3)
struct GUAH {// handler for initial collection of guas 2 3

	struct GUA {
		uint64_t tua[128];
		uint32_t nua, type, i81;
		inline void Add(uint64_t ua) {
			if (nua < 128)tua[nua++] = ua;
		}
		inline void AddIf(uint64_t ua) {
			for (uint32_t i = 0; i < nua; i++) {
				if (ua == tua[i]) return;
			}
			if (nua < 128)tua[nua++] = ua;
		}

		inline void Init(uint32_t n, uint32_t t, uint32_t i) {
			nua = n; type = t; i81 = i;
		}
		int Load(uint64_t* tu, uint64_t bf) {
			int n = 0;
			register uint64_t nbf = ~bf;
			for (uint32_t i = 0; i < nua; i++) {
				register uint64_t U = tua[i], cc = _popcnt64(U);
				if (n > 10) break;// 
				if (n > 5 && cc > 12) break;// 
				if (!(U & nbf))tu[n++] = U;
			}
			return n;
		}
		void SortClean(uint32_t lim=40) {
			if (nua < 2)return;
			GUA w = *this;
			BF128 vsize[30];
			memset(vsize, 0, sizeof vsize);
			uint64_t tcopy[128];
			memcpy(tcopy, w.tua, sizeof tcopy);
			for (uint32_t i = 0; i < nua; i++) {
				register uint64_t  cc = _popcnt64(tua[i] & BIT_SET_2X);
				vsize[cc].setBit(i);
			}
			nua = 0;
			for (int i = 0; i < 20; i++) if (vsize[i].isNotEmpty()) {
				int j;
				BF128 v = vsize[i];
				while ((j = v.getFirst128()) >= 0) {
					v.clearBit(j);
					register uint64_t U = tcopy[j];
					for (uint32_t k = 0; k < nua; k++) {
						register uint64_t U2 = tua[k];
						if (!(U & (~U2))) { U = 0; break; }
					}
					if (U) tua[nua++] = U;
					if (nua > lim) break;
				}
				if (nua > lim) break;
			}

		}
		void Debug(int nodet = 1) {
			cout << "gua type=" << type << " i81=" << i81
				<< "\tnua=" << nua << endl;
			if (nodet) return;
			for (uint32_t i = 0; i < nua; i++) {
				cout << Char2Xout(tua[i]) << " " << _popcnt64(tua[i] & BIT_SET_2X)
					<< " " << i << endl;
			}
		}
	}tg2[81], tg3[81], guaw;
	void Init() {
		for (int i = 0; i < 81; i++) {
			tg2[i].Init(0, 0, i); tg3[i].Init(0, 1, i);
		}
	}
	inline void Add2(uint64_t u, uint32_t i) { if (_popcnt64(u) < 18)		tg2[i].Add(u); }
	inline void Add3(uint64_t u, uint32_t i) { if (_popcnt64(u) < 18)		tg3[i].Add(u); }

	int IsUa4(int i81) {
		GUA& g = tg2[i81];
		if (g.nua == 1 && _popcnt64(g.tua[0]) == 2) return 1;
		return 0;
	}
	int IsUamin(int i81) {
		GUA& g = tg3[i81];
		if (g.nua == 1 && _popcnt64(g.tua[0]) < 5) return 1;
		return 0;
	}

	void SortClean3() {
		for (int i = 0; i < 81; i++)
			if (tg3[i].nua > 1) tg3[i].SortClean();
	}
	void SortClean(uint32_t lim = 40) {
		for (int i = 0; i < 81; i++)
			if (tg2[i].nua > 1) tg2[i].SortClean(lim);
	}

	int CutG2x(int lim) {
		int n = 0;
		for (int i = 0; i < 81; i++) {
			if ((int)tg2[i].nua > lim)tg2[i].nua = lim;
			n += tg2[i].nua;
		}
		return n;
	}
	int CutG3x(int lim) {
		int n = 0;
		for (int i = 0; i < 81; i++) {
			if ((int)tg3[i].nua > lim)tg3[i].nua = lim;
			n += tg3[i].nua;
		}
		return n;
	}
	void Dump2all2() {
		for (int i = 0; i < 81; i++) if (tg2[i].nua) {
			tg2[i].Debug(0);
		}
	}
	void Dump2all3() {
		for (int i = 0; i < 81; i++) if (tg3[i].nua) {
			tg3[i].Debug(0);
		}
	}
	void DumpOne2(int i) {
		cout << "debug2 i_1=" << i << endl;
		if (tg2[i].nua) 			tg2[i].Debug(0);
	}

	void DumpOne3(int i) {
		cout << "debug3 i_1=" << i << endl;
		if (tg3[i].nua) 			tg3[i].Debug(0);
	}
}guah;
struct GUAH54N {
	struct Z128 {// for one gua2/gua3
		BF128 	vc[54], vi[27],// vectore/cell /i81
			v0, //active items in vector
			v3,v6, v9; // v0 after clues
		uint64_t killer,t[128];
		uint32_t mode2_3, i81, n;
		void Init(uint32_t m2_3, uint32_t ix) {
			memset(vc, 255, sizeof vc);
			memset(&v0, 0, sizeof v0);
			mode2_3 = m2_3;
			i81 = ix;
			n = 0;
			killer = ~0;
		}
		void EnterInit(uint64_t u) {
			t[n] = u;
			uint32_t nr = n++;
			killer &= u;
			v0.setBit(nr);
			register uint32_t cell;
			register uint64_t U = u;
			while (bitscanforward64(cell, U)) {
				U ^= (uint64_t)1 << cell;
				vc[cell].clearBit(nr);
			}
		}
		void EnterFresh(uint64_t u);
		void Dump(int det=0) {
			cout << "dump mode " << mode2_3 << " i81" << i81 << endl;
			cout << Char54out(killer) << " killer" << endl;
			if (det > 1)
				for (uint32_t i = 0; i < 128; i++) {
					if (v0.Off(i))break;
					for (int j = 0; j < 54; j++)
						if (vc[j].On(i)) cout << ".";
						else cout << "1";
					cout << "  " << i << endl;
				}
			if (det > 2) {
				v0.Print(" v0");
				v3.Print(" v3");
				v6.Print(" v6");
			}
		}
		void Dumpv6(int det = 0) {
			cout << "dump mode " << mode2_3 << " i81" << i81 << endl;
			cout << Char54out(killer) << " killer" << endl;
			if (det > 1)
				for (uint32_t i = 0; i < 128; i++) {
					if (v0.Off(i))break;
					if (v6.On(i))continue;

					for (int j = 0; j < 54; j++)
						if (vc[j].On(i)) cout << ".";
						else cout << "1";
					cout << "  " << i << endl;
				}
			if (det > 2) {
				v0.Print(" v0");
				v3.Print(" v3");
				v6.Print(" v6");
			}
		}
		void DumpFiltered(uint64_t u) {
			for (uint32_t i = 0; i < 128; i++) {
				if (v0.Off(i))break;
				char ws[55], aig = 1;
				memset(ws, '.', sizeof ws); ws[54] = 0;
				for (uint64_t j = 0, bit = 1; j < 54; j++, bit <<= 1) {
					if (vc[j].On(i)) continue;
					if (bit & u) { aig = 0; break; }
					else ws[j] = '1';
				}
				if(aig)cout<<ws  << "  " << i << endl;
			}

		}
		int Redundant(uint64_t u) {
			for (uint32_t i = 0; i < 128; i++) {
				if (v0.Off(i))return 0;
				register uint64_t uc = 0, bit = 1;
				for (int j = 0; j < 54; j++,bit<<=1)
					if (vc[j].Off(i)) uc|=bit;
				if(u==uc )return 1;
			}
			return 0;
		}

	}zz[162];
	
	struct BLOC0 {// only one ua maxi 16
		uint64_t ua, id;
	}bloc0[40];
	uint32_t nbl0, nzzused, nzzg2;
	uint32_t tind6[162], ntind6;
	uint32_t tind9[162], ntind9;
	uint32_t tg2[90], ntg2, ntg2l, tmg2[20], ntmg2;
	uint32_t tg3[90], ntg3, ntg3l, tmg3[20], ntmg3;
	BF128 g2, g3,g2_6,g3_6,g2l,g3l;
	int indg2[81], indg3[81];
	uint64_t  gtul[GTULSIZE];// just before last one table
	uint32_t  ngtul;
	//____________________________________
	void Init() {	
		nbl0 = nzzused =0;	
		memset(indg2, 255, sizeof indg2);
		memset(indg3, 255, sizeof indg3);
	}
	inline void InitCom() { ntmg2 = ntmg3 = 0;}
	void Build();	void Build3();	void Build6(); void Build9();
	void Build6( uint32_t* tc) {
		g2_6.SetAll_0(); g3_6 = g2_6;
		ntind6 = 0;
		for (uint32_t i = 0; i < nzzused; i++) {
			Z128& myz = zz[i];
			//BF128 v = myz.v0;
			BF128 v= myz.vc[tc[0]];
			for (int j = 1; j < 6; j++)
				v &= myz.vc[tc[j]];
			myz.v6 = v; myz.v9 = v;
			if ((v & myz.v0).isNotEmpty()) {
				tind6[ntind6++] = i;
				if (myz.mode2_3) g3_6.setBit(myz.i81);
				else g2_6.setBit(myz.i81);
			}
		}
	}
	void Build9last(); void Build10last();
	inline void AddBuildlast(int ix);
	inline void AddBuildGet(int ix);
	inline void AddBuildGet2(int ix,int mode);

	inline void GetG2G3A(uint64_t bf) {
		g2.SetAll_0(); g3 = g2;
		ntg2 = ntg3 = 0;		
		// see bloc 0
		for (uint32_t i = 0; i < nbl0; i++) {
			if (!(bf & bloc0[i].ua)) {
				register uint32_t ix = (int)bloc0[i].id;
				if (ix >= 100) {// this is a g3
					ix -= 100;
					g3.setBit(ix);
					tg3[ntg3++] = ix;
				}
				else {
					g2.setBit(ix);
					tg2[ntg2++] = ix;
				}
			}
		}
		
	}
	void GetG2G3_7(); void GetG2G3_8();	void GetG2G3_9(); 
	void GetG2G3_10(); void GetG2G3_10last();
	void GetG2G3_11();
	void GetG2G3_12(uint64_t bf, uint32_t* tc) {
		GetG2G3A(bf);
		{
			for (uint32_t it = 0; it < ntind9; it++) {
				Z128& myz = zz[tind9[it]];
				if (bf & myz.killer) continue;
				BF128 v = (myz.v9 & myz.v0);
				for (uint32_t j = 0; j < 3; j++)
					v &= myz.vc[tc[j]];
				if (v.isNotEmpty()) {
					register uint32_t ix = myz.i81;
					if (myz.mode2_3) {// this is a g3
						g3.setBit(ix);
						tg3[ntg3++] = ix;
					}
					else {
						g2.setBit(ix);
						tg2[ntg2++] = ix;
					}
				}
			}
		}
	}

	inline void AddA2(uint64_t bf, uint64_t i81,int cc12){
		if (ngtul < GTULSIZE) gtul[ngtul++] = bf | i81 << 54;
		register Z128& mz = zz[indg2[i81]];
		if (mz.n < 128) mz.EnterFresh(bf);
	}
	inline void AddA3(uint64_t bf, uint64_t  i81) {
		if (ngtul < GTULSIZE) gtul[ngtul++] = bf | (i81+100) << 54;
		register Z128& mz= zz[indg3[i81]];
		if (mz.n< 128) mz.EnterFresh(bf);
	}

	void Add(uint64_t bf, BF128* vc, BF128 & v0,
		char * ix,	int32_t n, int32_t i81) {
		v0.setBit(n);
		ix[n] = i81;
		register uint32_t cell;
		register uint64_t U = bf;
		while (bitscanforward64(cell, U)) {
			U ^= (uint64_t)1 << cell;
			vc[cell].clearBit(n);
		}
	}
	void Status(int det = 0) {
		uint32_t nn = nbl0;
		cout << "GUAH54N status nbl0=" << nbl0 << "  nzzused=" << nzzused << endl;
		if (det)
			for (uint32_t i = 0; i < nbl0; i++)
				cout << Char54out(bloc0[i].ua) << " " << bloc0[i].id << endl;
		for (uint32_t i = 0; i < nzzused; i++) {
			Z128& myz = zz[i];
			if (det) {
				cout << myz.mode2_3 << " " << myz.i81 << "\t"
					<< " n=" << myz.n << endl;
				if (det > 1) {
					cout << Char54out(myz.killer) << " killer" << endl;
					myz.Dump(det);
				}
			}
			nn += myz.n;
		}
		cout << "total g2+g3 = " << nn << endl;
	}
	void Statusgx() {
		cout << " get g2 g3 result" << endl;
		for (uint32_t i = 0; i < ntg2; i++) cout << tg2[i] << " ";
		cout << " g2 list" << endl;
		g2.Print("g2");
		for (uint32_t i = 0; i < ntg3; i++) cout << tg3[i] << " ";
		cout << " g3 list" << endl;
		g3.Print("g3");
	}
	void Statusv6(int det=0) {
		cout << "v6 status still active end " << ntind6 << endl;
		for (uint32_t i = 0; i < nzzused; i++) {
			Z128& myz = zz[i];
			cout << myz.mode2_3 << " " << myz.i81 << endl;
			if (det)myz.Dumpv6(det);;
		}
	}
	void Statusv9() {
		cout << "v9 status still active end " << ntind9 << endl;
		for (uint32_t it = 0; it < ntind6; it++) {
			Z128& myz = zz[tind6[it]];
			cout <<myz.mode2_3<<" "<<myz.i81 << endl;
			myz.v9.Print("v9");
		}
	}
	void StatusFiltered(uint64_t u) {
		cout << "GUAH54N status filtered"<< endl;
		for (uint32_t i = 0; i < nzzused; i++) {
			Z128& myz = zz[i];
			if (myz.killer & u)continue;
			cout << myz.mode2_3 << " " << myz.i81 << "\t"
					<< " n=" << myz.n << endl;
			myz.DumpFiltered(u);
				
			
		}
	}
	void Dumpgtul(int det=0) {
		cout << " gtul status n=" << ngtul << endl;
		if (!det) return;
		for (uint32_t i = 0; i < ngtul; i++) {
			register uint64_t U = gtul[i], id = U >> 54;
			cout << Char54out(U) << " " << id << endl;
		}
	}
}guah54n;

//_____ processing band3
struct XQ {//to build the UAs b3 to expand
	uint32_t t1a; //27 bits field common 2 pairs 
	uint32_t  critbf,fa,fb;
	uint32_t  * t2a, * t2b3,*t2b;
	uint32_t n2a, n2b,n2b3, nb3,bf3p,nmiss,nadded;
	uint32_t nin, nout, nred;
	uint32_t iuas4;
	uint32_t tbuf[60];
	uint32_t tin[400], tout[400],tred[300];
	void Init() { 
		t1a = critbf = 0;
		n2a = n2b = n2b3= bf3p = 0;
		nin=nout=nadded= 0; 
		t2a = tbuf; t2b3 = tbuf + 12; t2b = t2b3 + 24;
	}
	inline void SetFilters () {
		if (!nmiss) {
			if ((fa = t1a)) {// initial safety
				critbf = 0;
				for (uint32_t i = 0; i < n2b3; i++)
					critbf |= t2b3[i];
				for (uint32_t i = 0; i < n2b; i++)
					critbf |= t2b[i];
			}
			fb = critbf;
		}
		else {	fa = 0; fb = BIT_SET_27;}
	}
	int Miss1ToMiss0(int debug=0);
	int MissxToMiss0(uint32_t ubf);
	int Miss0CheckTin();
	int NoRoomToAssign() {
		return(_popcnt32(t1a) >= nb3);
	}
	int NToAssign() {
		return( nb3- _popcnt32(t1a));
	}
	inline void SetFreshCrit() {
		fb = 0;
		for (uint32_t i = 0; i < n2b; i++) {
			fb |= t2b[i];
		}
		critbf = fb;
	}
	uint32_t  AssignMiss0(uint32_t bf);

	uint32_t  AddAssigned(uint32_t bf) {
		nadded++;
		t1a |= bf;
		fa = t1a;
		register uint32_t F = t1a, C = 0,n=n2b;
		n2b = 0;
		for (uint32_t i = 0; i < n; i++) {
			register uint32_t U = t2b[i];
			if (!(U & F)) {
				t2b[n2b++]=U;
				C |= U;
			}
		}
		fb=critbf = C;
		return C;
	}
	inline void Addin(uint32_t bf) { tin[nin++] = bf; }
	inline void Addout(uint32_t bf) { tout[nout++] = bf; }
	inline uint32_t GetAndout() {
		register uint32_t A = tout[0];
		for (uint32_t i = 1; i < nout; i++)
			A&=tout[i];
		return A;
	}
	int AddRedundant(uint32_t bf) {
		register uint32_t nbf = ~bf;
		for (uint32_t i = 0; i < nred; i++) {
			register uint32_t u = tred[i];
			if (!(u & nbf)) return 0;// subset or =
			if (!(bf & ~u)) {
				tred[i]=bf; // new is subset
				return 1;// keep it as valid
			}
		}
		tred[nred++] = bf;
		return 1;
	}
	void BuildMiss0Redundant() {
		nred = n2b3+n2b;
		memcpy(tred, t2b3, n2b3 * sizeof tred[0]);
		memcpy(&tred[n2b3], t2b, n2b * sizeof tred[0]);
		int n = 0;
		for (uint32_t i = 0; i < nin; i++) {
			if (AddRedundant(tin[i]))
				tin[n++] = tin[i];;
		}
		nin = n;
	}
	void BuildMissxRedundant() {
		nred =n2a+ n2b3 + n2b;
		memcpy(tred, t2a, n2a * sizeof tred[0]);
		memcpy(&tred[n2a], t2b3, n2b3 * sizeof tred[0]);
		memcpy(&tred[n2a+n2b3], t2b, n2b * sizeof tred[0]);
		int n = 0;
		for (uint32_t i = 0; i < nin; i++) {
			if (AddRedundant(tin[i]))
				tin[n++] = tin[i];;
		}
		nin = n;
	}
	inline int SubCritMore(uint32_t F) {
		if (!F) return 0;
		register uint32_t ff = F, ret = 0;
		for (uint32_t i = 0; i < n2a; i += 2) {
			register uint32_t a = t2a[i], b = t2a[i + 1],
				mask = a | b, f = mask & F;
			if (f) {
				ff &= ~(mask & F);
				int cc = _popcnt32(f);
				if (cc > 1)ret += _popcnt32(f) - 1;
				else if (f &= ~(a & b)) ret++;
				//f &= ~(a & b); // clues extra mincount
				//ret += _popcnt32(f)-1;
			}
		}
		if (ret > 1 || !ff) return ret; 
		for (uint32_t i = 0; i < n2b3; i += 3) {
			register uint32_t mask = t2b3[i] | t2b3[i + 1]| t2b3[i + 2],
				f = mask & F;
			if (f) {
				if (f == mask) ret++;
				ff &= ~(mask & F);	
			}
		}
		if (ret > 1||!ff) return ret;// already to many
		// others are disjoints
		for (uint32_t i = 0; i < n2b; i++) {
			register uint32_t a = t2b[i] & ff;
			if (a) 	ret += (_popcnt32(a) - 1);
		}
		return ret;
	}
	void SubCritMoreDo(uint32_t F) {// 1 more to process
		// clean all hits
		register uint32_t nn = n2a;
		n2a = 0;
		for (uint32_t i = 0; i < nn; i += 2) {
			register uint32_t a = t2a[i], b = t2a[i + 1];
			if (!((a | b ) & F)) {
				t2a[n2a++] = a; t2a[n2a++] = b;
			}
			else {
				if (!(a & F))t2b[n2b++] = a;
				if (!(b & F))t2b[n2b++] = b;
				t1a &= ~(a | b);
			}
		}
		nn = n2b3; n2b3 = 0; // Is it 3 pairs one minirow
		for (uint32_t i = 0; i < nn; i += 3) {
		 	register uint32_t a= t2b3[i],
				b= t2b3[i + 1],c= t2b3[i + 2];
			if (!((a | b | c) & F)) {
				t2b3[n2b3++] = a;
				t2b3[n2b3++] = b;
				t2b3[n2b3++] =c;
			}
			else {
				if (!(a & F))t2b[n2b++] = a;
				if (!(b & F))t2b[n2b++] = b;
				if (!(c & F))t2b[n2b++] = c;
			}	
		}
		// others are disjoints more if 2 clues
		nn = n2b;	n2b = 0;
		for (uint32_t i = 0; i < nn; i++) {
			register uint32_t a = t2b[i] ;
			if (!(a & F))t2b[n2b++] = a;
		}

	}
	inline uint32_t SubCritActive(uint32_t F) {
		register uint32_t ret = 0;
		for (uint32_t i = 0; i < n2a; i += 2) {
			register uint32_t a = t2a[i], b = t2a[i + 1],
				mask = a | b, f = mask & F;
			if (!f) ret |= mask;
		}
		for (uint32_t i = 0; i < n2b3; i ++)  
			if(!(F& t2b3[i]))ret |= t2b3[i];
		for (uint32_t i = 0; i < n2b; i++)
			if (!(F & t2b[i]))ret |= t2b[i];		
		return ret;
	}
	inline uint32_t NonHitOut(uint32_t F) {
		register uint32_t ret = 0;
		for (uint32_t i = 0; i < nout; i ++) 
			if (!(F&tout[i]) )return 1;
		return 0;
	}
	int IsNotRedundantOut(uint32_t bf) {
		register uint32_t nbf = ~bf;
		for (uint32_t i = 0; i < nout; i++) {
			register uint32_t u = tout[i];
			if (!(u & nbf)) return 0;// subset or =			
		}
		return 1;
	}
	void BuildMiss0Out() {
		nout = n2b3;
		nred = 0;
		memcpy(tout, t2b3, n2b3 * sizeof tred[0]);
		// pickup all 2 store more 
		for (uint32_t i = 0; i < n2b; i++) {
			register uint32_t u = t2b[i];
			if (_popcnt32(u) > 2) {
				tred[nred++] = u;
				continue;
			}
			tout[nout++] = u;
		}
		for (uint32_t i = 0; i < nin; i++) {
			register uint32_t u = tin[i];
			if (_popcnt32(u) > 2) {
				tred[nred++] = u;
				continue;
			}
			if(IsNotRedundantOut(u))
				tout[nout++] = u;
		}
		for (uint32_t i = 0; i < nred; i++) {
			register uint32_t u = tred[i];
			if (IsNotRedundantOut(u))
				tout[nout++] = u;
		}

	}
	void BuildMissxOut() {
		register uint32_t* tt = tout + nout;
		memcpy(tt, t2a, n2a * sizeof tred[0]);
		tt += n2a;
		memcpy(tt, t2b3, n2b3 * sizeof tred[0]);
		tt += n2b3;
		memcpy(tt, t2b, n2b * sizeof tred[0]);
		nout =(int) (tt - tout) + n2b;
		for (uint32_t i = 0; i < nin; i++) {
			register uint32_t u = tin[i];
			if (IsNotRedundantOut(u))
				tout[nout++] = u;
		}
		nin = 0;
	}


	void BuildCheckRedundant() {
		nred = n2b;
		if (nmiss) {
			nred += n2a;
			memcpy(&t2b[n2b], t2a, n2a * sizeof t2b[0]);
		}
	}
	uint64_t Isoutsize2();
	uint64_t Isoutsize3();
	uint64_t Isoutsize4();
	int NoDisjoint() {
		register uint32_t r1 = tout[0] , r2 ;
		for (uint32_t i = 1; i < nout; i++) {
			register uint32_t u = tout[i];
			if (r2 |= r1 & u)return 1; 
				r1 |= u;
		}
		return 0;
	}
	int Min1_4Disjoint();
	void CleanIn();
	void CleanOut();
	void CleanOut(uint32_t F, uint32_t A);
	void Dump1() {
		cout << "xq nmiss= " << nmiss<< " nb3="<<nb3 << endl;
		cout << Char27out(t1a) << "t1a bf2 to assign" << endl;
		cout << Char27out(critbf) << " critbf" << endl;
		cout << "___________________  2 pairs" << endl;
		for(uint32_t i=0;i<n2a;i++)
			cout << Char27out(t2a[i])  << endl;
		cout << "___________________  3 pairs" << endl;
		for (uint32_t i = 0; i < n2b3; i++)
			cout << Char27out(t2b3[i]) << endl;
		cout << "___________________  one hit" << endl;
		for (uint32_t i = 0; i < n2b; i++)
			cout << Char27out(t2b[i]) << endl;

	}
	void Dump2() {
		cout << Char27out(fa) << " F assigned" << endl;
		cout << Char27out(fb) << " fb active" << endl;
		cout << Char27out(critbf) << " critbf" << endl;
	}
	void DumpOut() {
		cout << "out status nout=" <<nout<< endl;
		for (uint32_t j = 0; j < nout; j++)
			cout << Char27out(tout[j])<< " "<<j << endl;

	}

	void Status() {
		Dump1(); //Dump2();
		cout << " nadded= " << nadded 
			<<" nout="<<nout << endl;
		for (uint32_t i = 0; i < nout; i++)
			cout << Char27out(tout[i]) << endl;
		cout << " nin=" << nin << endl;
		for (uint32_t i = 0; i < nin; i++)
			cout << Char27out(tin[i]) << endl;
		cout << "end xq status \n" << endl;
	}
	void Statusmiss0(uint32_t F, uint32_t A) {
		cout << Char27out(F) << " F" << endl; 
		cout << Char27out(A) << " A" << endl;
		cout << "___________________  3 pairs" << endl;
		for (uint32_t i = 0; i < n2b3; i++)
			cout << Char27out(t2b3[i]) << endl;
		cout << "___________________  one hit" << endl;
		for (uint32_t i = 0; i < n2b; i++)
			cout << Char27out(t2b[i]) << endl;
		cout << " nin=" << nin << endl;
		for (uint32_t i = 0; i < nin; i++)
			cout << Char27out(tin[i]) << endl;
		cout << " nout=" << nout << endl;
		for (uint32_t i = 0; i < nout; i++)
			cout << Char27out(tout[i]) << endl;
		cout << "end xq status \n" << endl;
	}
}xq;

// standard  bands  
struct STD_B416 {
	char band[28];// band in char mode
	int i416,// id 0-415 in minlex mode of the band
		map[27],// mapping cells from minlex to solution grid
		band0[27], // band in 0-8 integer mode
		gangster[9], // bit field digits per column
		dpat[9],// solution pat per digit
		dpmi[9],// initial map gangster per digit
		dband;
	uint32_t tua[82], nua;//  maximum 81 morphed uas 
	uint32_t fd_sols[2][9];//start puzzle/ solution
	void Initstd();// first band initial (once)
	void GetBandTable(int i416e);//pick up band 1 from table
	void InitG12(int i416e);// end init band 1 
	void InitBand2_3(int i16, char* ze, BANDMINLEX::PERM& p
		, int iband = 1);

	void SetGangster();
	inline void GetUAs() {
		nua = t16_nua[i416];
		memcpy(tua, &t16_UAs[t16_indua[i416]], 4 * nua);
	}
	void MorphUas();
	void InitC10(int i);// known mode


	void PrintStatus();
};
struct STD_B3 :STD_B416 {// data specific to bands 3
	// permanent gangster information
	struct G {
		BF128 gsocket2, gsocket3;// active i81 mode 81 bits
		BF128 gsocket4, gsocket6;//g2 with 4 cells in band 3
		BF128 gsocket2all;
		int pat2[81], pat3[81]; // storing ua bitfields
		int pat2_27[27]; // storing ua bitfields
		int ua2_imini[81], ua3_imini[81], ua2bit27[81];
	}g;
	char isg2[81],isg3[81];
	uint32_t  mg2, mg3,minc,ming2_1, ming2_2, ming2_3;
	int minirows_bf[9];
	int triplet_perms[9][2][3];
	uint32_t i_27_to_81[27], i_9_to_81[9]; //band i81 for guas guas3
	uint32_t i_81_to_27[81]; //band i81 for guas guas3
	uint32_t  poutdone, aigskip,
		tg2_4[50], ntg2_4, tg2_6[50], ntg2_6;
	//_______________________
	void InitBand3(int i16, char* ze, BANDMINLEX::PERM& p);
	void GoA();// start band 3  
	void GoAg23(int debug=0);// fresh g2 g3 to consider 
	void GoB0();// band3 miss0 at start
	void GoC0(uint32_t bf, uint32_t a);// band3 miss0 before guam guamm
	void GoC0F(uint32_t bf);//same nb3 filled
	void GoB1();//  band 3 miss1 at start
	void GoB1toMiss0(uint32_t bf);//  band 3 miss1 at start
	void GoBMore1();//  band 3 miss>1 at start
	void GoBMoretoMiss0(uint64_t ubf);
	void GoBMoretoMiss1(uint64_t ubf);


	uint32_t Get2d(int d1, int d2) {
		return fd_sols[0][d1] | fd_sols[0][d2];
	}
	inline int GetI81_2(int bf) {
		for (uint32_t i = 0; i < 27; i++) {
			register uint32_t i81 = i_27_to_81[i];
			if (g.pat2[i81] == bf) return i81;
		}
		return -1;
	}
	inline int GetI81_3(int bf) {
		for (uint32_t i = 0; i < 9; i++) {
			register uint32_t i81 = i_9_to_81[i];
			if (g.pat3[i81] == bf) return i81;
		}
		return -1;
	}
	inline int GetI81_x(int bf) {
		for (uint32_t i = 0; i < 81; i++) {
			if (g.pat2[i] == bf) return i;
		}
		return -1;
	}


	void Pat_to_digitsx(int bf, int* tcells, int* tdigits, int& nt) {
		register int cell;
		nt = 0;
		while (bitscanforward(cell, bf)) {
			bf ^= 1 << cell;
			tcells[nt] = cell;
			tdigits[nt++] = band0[cell];
		}
	}
	int Is_Pat_For_Mex(int* tcells, int* tdigits, int nt) {
		for (int i = 0; i < nt; i++) {
			if (band0[tcells[nt]] != tdigits[nt]) return 0;
		}
		return 1;
	}
	void DumpIndex() {
		cout << "index 27 to 81 " << endl;
		for (int i = 0; i < 27; i++) {
			register uint32_t i81 = i_27_to_81[i];
			cout << i << " i81=" << i81 << " " << Char27out(g.pat2[i81]) << endl;
		}
		cout << "index 9 to 81 " << endl;
		for (int i = 0; i < 9; i++) {
			register uint32_t i81 = i_9_to_81[i];
			cout << i << " i81=" << i81 << " " << Char27out(g.pat3[i81]) << endl;
		}

	}

#define GM_NB4 50
#define GM_NBM 50

	struct GUM64 {
		uint64_t v0,  vc[55];//vc[54] is for 6 clues
		uint32_t tb3[64], n;
		void Init() {
			n = 0;		v0 = 0;
			memset(vc, 255, sizeof vc);
			vc[54] = 0;
		}
		int Add(uint64_t bf, uint32_t patb3) {
			if (n >= 64) return 0;//safety
			tb3[n] = patb3;
			uint64_t bit = (uint64_t)1 << n++;
			v0 |= bit; vc[54] |= bit;
			register uint64_t B = bf, nbit = ~bit;
			int cell;
			while (bitscanforward64(cell, B)) {
				B ^= (uint64_t)1 << cell;
				vc[cell] &= nbit;
			}
			return 1;
		}
		inline void Set6(uint32_t* t) {
			register uint64_t v = v0;
			for (int i = 0; i < 6; i++) v &= vc[t[i]];
			vc[54] = v;
		}
		inline uint64_t Getv(uint32_t* t, int nt) {
			register uint64_t v = vc[54];
			for (int i = 0; i < nt; i++) v &= vc[t[i]];
			return v;
		}

		void Dump(int i0) {
			for (uint32_t i = 0; i < n; i++) {
				uint64_t bit = (uint64_t)1 << i;
				cout <<Char27out(tb3[i]) << "\t";
				for (int j = 0; j < 54; j++)
					if (vc[j] & bit) cout << ".";
					else cout << "1";
				cout << "  " << i + i0 << endl;
			}
		}

		uint64_t bf12;// mode 54
		uint32_t bf3;
		inline int Count() {
			return ((int)_popcnt64(bf12) + _popcnt32(bf3));
		}
		void Print() {
			cout << Char54out(bf12) << "\t";
			cout << Char27out(bf3)
				<< " " << Count() << endl;
		}
	}tgm64[GM_NB4], tgm64m[GM_NBM];
	uint32_t nbgm,  nbbgm, nbgmm, nbbgmm;
	void InitTg() {
		nbgm = nbbgm =  0;
		nbgmm = nbbgmm = 0;
		for (int i = 0; i < GM_NB4; i++) tgm64[i].Init();
		for (int i = 0; i < GM_NBM; i++) tgm64m[i].Init();
	}
	inline void Addm4(BF128 &w) {// entry mode 3x
		if (nbgm >= 64 * GM_NB4) return;
		nbbgm = nbgm++ >> 6; // new last bloc 
		register uint64_t U = w.bf.u64[0];
		U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
		tgm64[nbbgm].Add(U, w.bf.u32[2]);
	}
	inline void Addmm(BF128& w) {// entry mode 3x
		if (nbgmm >= 64 * GM_NBM) return;
		nbbgmm = nbgmm++ >> 6; // new last bloc 
		register uint64_t U = w.bf.u64[0];
		U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
		tgm64m[nbbgmm].Add(U, w.bf.u32[2]);
	}

	inline void Set6clues(uint32_t * tc) {
		for (uint32_t i = 0; i <= nbbgm; i++) 
			tgm64[i].Set6(tc);
		for (uint32_t i = 0; i <= nbbgmm; i++) 
				tgm64m[i].Set6(tc);
	}

};


//____ entry builder
void BandReShape(int* s, int* d, BANDMINLEX::PERM p);
void BandReOrder(int* d);
struct GEN_BANDES_12 {// encapsulating global data 
	STD_B3 bands3[512];
	int sgchecked[512][81], nsgchecked;// used in pass1 band3 <=
	int modeb12, go_back, diagmore, diagbug, ip20,
		it16, it16_2, it16_3, imin16_1, imin16_2, imin16_3;
	int i1t16, i2t16, i3t16,// index 416 ordered in increasing size of valid clues 3
		ixmin1, ixmin2, ixmin3, maxnb3;
	int irtw2,iret_diag;
	char zsol[82], rband2[28];
	int grid0[81],grid1[81], gw[81], tc[6], ntc;

	int gcheck[82], ib1check, ib2check, ib3check, ibasecheck;
	uint64_t   nb12;
	int sliceread, current_slice, bit_slice, maxbits;
	BANDMINLEX::PERM *t_auto_b1, * t_auto_p1,// maxi is 107
		t_auto_b1b2[108], t_auto_b2b1[108],
		pband2, pband3, pcheck2, pcheck3;
	int n_auto_b1, n_auto_p1, n_auto_b1b2, n_auto_b2b1;
	int cold[9], coldf[9], rowd[6], boxd[6], rowdb3[3], boxdb3[3]; //free digits 
	//_________________ gangster 
	int gangcols[9];// 9 bits fields band3 for each colum (see valid band2)
	int gangb12[9]; // digit bf bands 12 per column


	struct B1B2 {
		int z0[54], z1[54], ntab1b2;
		BANDMINLEX::PERM tab1b2[108];
		int Compare54(int* o) {
			for (int i = 0; i < 54; i++) {
				if (o[i] > z0[i]) return 1;
				if (o[i] < z0[i]) return -1;
			}
			return 0;
		}
		void Init(int* o) {	memcpy(z0, o, sizeof z0);	}
		int Check(GEN_BANDES_12& o) {
			int* z = &z0[27];
			for (int imorph = 0; imorph < o.n_auto_b1; imorph++) {
				BANDMINLEX::PERM& p = o.t_auto_b1[imorph];
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(&o.grid0[27], band);
				if (ir > 1) continue;		if (ir == 1) return 1;
				tab1b2[ntab1b2++] = p;
			}
			return 0;
		}
		int  Initb2b1(GEN_BANDES_12& o) {
			memcpy(z0, o.grid0, sizeof z0);
			BANDMINLEX::PERM& p = o.pband2;
			int zt[27];
			BandReShape(z0, zt, p);
			memcpy(&z0[27], zt, sizeof zt);
			return  Compare54(o.grid0);
		}
		int Check3(int * zc,int * z) {// z is band3 to check
			for (int imorph = 0; imorph < ntab1b2; imorph++) {
				BANDMINLEX::PERM& p = tab1b2[imorph];
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(zc, band);
				if (ir > 1) continue;		if (ir == 1) return 1;
			}
			return 0;
		}
	}wb1b2,wb2b1;

	struct TWW {
		int zs0[81], zs1[81], ib[3], ibx[3],*zco;
		BANDMINLEX::PERM perm_ret;
		void PermB( int i1, int i2) {
			register int ix = ib[i1];  ib[i1] = ib[i2]; ib[i2] = ix;
			ix = ibx[i1];  ibx[i1] = ibx[i2]; ibx[i2] = ix;
			int temp[27];
			memcpy(temp, &zs0[27 * i1], sizeof temp);
			memcpy(&zs0[27 * i1], &zs0[27 * i2], sizeof temp);
			memcpy(&zs0[27 * i2], temp, sizeof temp);
		}
		void RigthOrder() {
			if (ibx[1] < ibx[0])PermB(  0, 1);
			if (ibx[2] < ibx[0])PermB(  0, 2);
			if (ibx[2] < ibx[1])PermB(  1, 2);
		}
		void MorphToB1() {
			BandReShape(zs0, zs1, perm_ret);
			BandReShape(&zs0[27], &zs1[27], perm_ret);
			BandReShape(&zs0[54], &zs1[54], perm_ret);
		}
		void MorphToB1First() {
			bandminlex.Getmin(zs0, &perm_ret);
			MorphToB1();
			memcpy(zs0, zs1, sizeof zs0);
		}
		void InitD(int * o) {
			for (int i = 0; i < 81; i++)
				zs0[i] = o[C_transpose_d[i]];
			bandminlex.Getmin(zs0, &perm_ret);
			ib[0] = perm_ret.i416; ibx[0] = t416_to_n6[ib[0]];
			bandminlex.Getmin(&zs0[27], &perm_ret);
			ib[1] = perm_ret.i416; ibx[1] = t416_to_n6[ib[1]];
			bandminlex.Getmin(&zs0[54], &perm_ret);
			ib[2] = perm_ret.i416; ibx[2] = t416_to_n6[ib[2]];
			RigthOrder();
		}
		void Init(int* o) {	memcpy(zs0, o, sizeof zs0);	}
		void InitPermb1b2(int* o) {
			memcpy(zs0, o, sizeof zs0);
			PermB(0, 1);	MorphToB1First();	}
		void InitPermb3(int* o) {// a;b;c to c;a;b
			memcpy(zs0, o, sizeof zs0);
			PermB(0, 2); PermB(1,2);
			MorphToB1First();
		}
		void PushComToMinimal(GEN_BANDES_12& o) {	
			MorphToB1First();// zs1 is also morphed
			if (!o.n_auto_b1) return;
			for (int imorph = 0; imorph < o.n_auto_b1; imorph++) {
				BANDMINLEX::PERM& p = o.t_auto_b1[imorph];
				int* z = &zs0[27];// morph the band
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(&zs1[27], band);
				if (ir > 1) continue;
				if (ir == 1) {// new mini save and morph b3
					BandReOrder(band);
					memcpy(&zs1[27], band, sizeof band);
					BandReShape(&zs0[54], &zs1[54], p);
					continue;
				}
				else {	// same b1b3 must check b2
					int* z = &zs0[54];// morph the band
					SKT_MORPHTOP
						if (G17ComparedOrderedBand(&zs1[54], band) > 1) {
							BandReOrder(band);
							memcpy(&zs1[54], band, sizeof band);
						}
				}
			}
			memcpy(zs0, zs1, sizeof zs0);
		}
		void PushP2bToMinimal(GEN_BANDES_12& o, int* g, int mode = 0) {
			memcpy(zs0, g, sizeof zs0);
			switch (mode) { //abc => 
			case 0:PermB(0, 2); PermB(1, 2); break;//cab
			case 1: PermB(0, 2);  break; // cba 
			case 2:PermB(1, 2); break; // acb 
			case 3: PermB(1, 2); PermB(0, 2); break; // bca 
			case 4:PermB(0, 1); break; // bac 
			case 5:break;// do nothing
			}
			PushComToMinimal(o);	
		}
		void MorphToP1(GEN_BANDES_12& o) {
			memcpy(zs0, o.grid0, sizeof zs0);
			PermB(0, 2);//cba
			PermB(1, 2);//now cab
			MorphToB1First();// zs1 is also morphed
			memcpy(o.grid1, zs1, sizeof zs0);
		}
		void MorphToP2b(GEN_BANDES_12& o) {
			memcpy(zs0, o.grid0, sizeof zs0);
			PermB(1, 2);//now acb
			MorphToB1First();// zs1 is also morphed
			memcpy(o.grid1, zs1, sizeof zs0);
		}
		int IsBelowGrid1(GEN_BANDES_12& o, int* g, int mode = 0) {
			memcpy(zs0, g, sizeof zs0);
			switch (mode) { //abc => 
			case 0:PermB(1, 2); break; // acb  Bx2=Bx3
			case 1:PermB(0, 1); break; // bac  Bx1=Bx2
				// now if 3 bands same Bx
			case 2:PermB(0, 2); PermB(1, 2); break;//cab
			case 3: PermB(0, 2);  break; // cba 
			case 4: PermB(1, 2); PermB(0, 2); break; // bca 
			case 5:break;// do nothing
			case 6:PermB(1, 2); PermB(0, 1); break;// bac on diag p2a
			}
			MorphToB1First();// zs1 is also morphed
			if (Compare(o.grid1) > 0) return 1;
			if (!o.n_auto_p1) return 0;
			for (int imorph = 0; imorph < o.n_auto_p1; imorph++) {
				BANDMINLEX::PERM& p = o.t_auto_p1[imorph];
				int* z = &zs0[27];// morph the band
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(&zs1[27], band);
				if (ir > 1) continue;
				if (ir == 1) {// new mini save and morph b3
					BandReOrder(band);
					memcpy(&zs1[27], band, sizeof band);
					if (Compare54(o.grid1) > 0) return 10 + imorph;
				}
				BandReShape(&zs0[54], &zs1[54], p);
				if (Compare(o.grid1) > 0) return 20 + imorph;
			}
			return 0;
		}
		int IsBelowMoreP2a(GEN_BANDES_12& o, int* g, int mode) {
			memcpy(zs0, g, sizeof zs0);
			switch (mode) { //abc =>  abc bac acb done direct
			case 0:PermB(0, 2); PermB(1, 2); break;//cab
			case 1: PermB(0, 2); break; // cba 
			case 2: PermB(1, 2); PermB(0, 2); break; // bca 
			case 3:PermB(1, 2); break; // acb 
			case 4:PermB(0, 1); break; // bac 
			}
			MorphToB1First();// zs1 is also morphed
			if (Compare(o.grid0) > 0) return 1;
			if (!o.n_auto_b1) return 0;
			for (int imorph = 0; imorph < o.n_auto_b1; imorph++) {
				BANDMINLEX::PERM& p = o.t_auto_b1[imorph];
				int* z = &zs0[27];// morph the band
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(&zs1[27], band);
				if (ir > 1) continue;
				if (ir == 1) {// new mini save and morph b3
					BandReOrder(band);
					memcpy(&zs1[27], band, sizeof band);
					if (Compare54(o.grid0) > 0) return 10+imorph;
				}
				BandReShape(&zs0[54], &zs1[54], p);
				if (Compare(o.grid0) > 0) return 20 + imorph;
			}
			return 0;
		}
		int IsBelowP1(GEN_BANDES_12& o) {
			int ir = Compare0(o.grid0);
			if (ir > 0) return 1; // smaller
			if (!o.n_auto_b1) return 0;
			for (int imorph = 0; imorph < o.n_auto_b1; imorph++) {
				int  z[27];
				memcpy(z, &zs0[27], sizeof z);
				BANDMINLEX::PERM& p = o.t_auto_b1[imorph];
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(&o.grid0[27], band);
				if (ir > 1) continue;		if (ir == 1) return 1;
				// same b2 must check b3
				memcpy(z, &zs0[54], sizeof z);
				{	SKT_MORPHTOP
					if (G17ComparedOrderedBand(&o.grid0[54], band) == 1) return 1;
				}
			}
			return 0;
		}
		int IsBelowP2a();
		int Compare0(int* o) {
			for (int i = 0; i < 81; i++) {
				if (o[i] > zs0[i]) return 1;
				if (o[i] < zs0[i]) return -1;
			}
			return 0;
		}
		int Compare(int* o) {
			for (int i = 0; i < 81; i++) {
				if (o[i] > zs1[i]) return 1;
				if (o[i] < zs1[i]) return -1;
			}
			return 0;
		}
		int Compare54(int* o) {
			for (int i = 0; i < 54; i++) {
				if (o[i] > zs1[i]) return 1;
				if (o[i] < zs1[i]) return -1;
			}
			return 0;
		}


		void DumpP1(char* const lib) {
			for (int i = 0; i < 81; i++) cout << zs0[i] + 1;
			cout << lib  << endl;
		}

	}tww,tww2;

	struct TWW1:TWW  {// diagonal morph check
		int IsDiagBelow(GEN_BANDES_12& o) {// same band index with auto morph
			if (!o.n_auto_b1) return 0;
			for (int imorph = 0; imorph < o.n_auto_b1; imorph++) {
				int  z[27];
				memcpy(z, &zs0[27], sizeof z);
				BANDMINLEX::PERM& p = o.t_auto_b1[imorph];
				SKT_MORPHTOP
					int ir = G17ComparedOrderedBand(&o.gcheck[27], band);
				if (ir > 1) continue;		if (ir == 1) return 1;
				// same b2 must check b3
				memcpy(z, &zs0[54], sizeof z);
				{	SKT_MORPHTOP
					if (G17ComparedOrderedBand(&o.gcheck[54], band) == 1) return 1;
				}
			}
			return 0;
		}
		int CheckDiag(GEN_BANDES_12& o) {
			InitD(o.gcheck);
			if (ibx[0] < o.i1t16) return 1;
			if (ibx[0] > o.i1t16) return 0;
			if (ibx[1] < o.i2t16) return 1;
			if (ibx[1] > o.i2t16) return 0;
			if (ibx[2] < o.i3t16) return 1;
			if (ibx[2] > o.i3t16) return 0;
			// same both ways could use automorphs to reduce more
			MorphToB1First();
			int ir = Compare(o.gcheck);
			if (ir > 0) return 1; // diag smaller
			if (IsDiagBelow(o))return 1;// auto morphs
			if (o.i1t16 == o.i2t16) 	PermB(0, 1);
			else if (o.i3t16 == o.i2t16) 	PermB(1, 2);
			else return 0;
			MorphToB1First();
			ir = Compare(o.gcheck);
			if (ir > 0) return 1; // diag smaller
			if (IsDiagBelow(o))return 1;
			return 0;
		}
		int CheckDiagP1(GEN_BANDES_12& o) {
			InitD(o.grid0);
			//Dump(" dp1 ");
			if (ibx[0] < o.i3t16) return 1;
			if (ibx[0] > o.i3t16) return 0;
			if (ibx[1] < o.i1t16) return 1;
			if (ibx[1] > o.i1t16) return 0;
			if (ibx[2] < o.i2t16) return 1;
			if (ibx[2] > o.i2t16) return 0;
			// same both ways order in pass1 mode 
			PermB(0, 1); PermB(1, 2);
			MorphToB1First();
			return 2;
		}
		int CheckDiagPmin();
		int CheckDiagP2a();
		int CheckDiagP2aMore_abc();
		int CheckDiagP2b(GEN_BANDES_12& o) {
			InitD(o.grid0);
			if (ibx[0] < o.i1t16) return 1;
			if (ibx[0] > o.i1t16) return 0;
			if (ibx[1] < o.i3t16) return 1;
			if (ibx[1] > o.i3t16) return 0;
			if (ibx[2] < o.i2t16) return 1;
			if (ibx[2] > o.i2t16) return 0;
			// same both ways order in pass1 mode 
			PermB(1, 2);
			MorphToB1First();
			return 2;
		}
		void Dump(char* const lib) {
			for (int i = 0; i < 81; i++) cout << zs0[i] + 1;
			cout << lib <<"\t" << ibx[0] << " " << ibx[1] << " " << ibx[2] << "\t"
				<< ib[0] << " " << ib[1] << " " << ib[2]	 << endl;
		}

	}tww1;


	int GET_I81_G2(int digs, uint32_t pat) {
		register  uint32_t A = pat,
			B = (A | (A >> 9) | (A >> 18)) & 0777; // all columns
		uint32_t dstack;
		bitscanforward(dstack, B);
		dstack = (dstack / 3) * 27;// now stack0 0, 27 57 chunks of 27 i81
		for (uint32_t i = dstack; i < dstack + 27; i++)
			if (digs == tsgua2[i].digs) return i;
		return 0; // would be a bug
	}
	int GET_I81_G2_4(int digs, uint32_t pat) {
		register  uint32_t A = pat,
			B = (A | (A >> 9) | (A >> 18)) & 0777; // all columns
		// keep the stack with 2 columns
		for (int i = 0, mask = 7; i < 3; i++, mask <<= 3) {
			if (_popcnt32(B & mask) == 2) {
				B = mask;
				break;
			}
		}
		uint32_t dstack; // now same as pat 2 cells
		bitscanforward(dstack, B);
		dstack = (dstack / 3) * 27;// now stack0 0, 27 57 chunks of 27 i81
		for (uint32_t i = dstack; i < dstack + 27; i++)
			if (digs == tsgua2[i].digs) return i;
		return 0; // would be a bug
	}

	int GET_I81_G3(int digs, uint32_t pat) {
		register  uint32_t A = pat,
			B = (A | (A >> 9) | (A >> 18)) & 0777; // all columns
		uint32_t dstack;
		bitscanforward(dstack, B);
		dstack = (dstack / 3) * 27;// now stack0 0, 27 57 chunks of 27 i81
		for (uint32_t i = dstack; i < dstack + 27; i++)
			if (digs == tsgua3[i].digs) return i;
		return 0; // would be a bug
	}

	// __________________________  primary UAs tables and creation of such tables
	uint64_t* ptua2;// pointer to current table cycle search 2/3
	uint32_t   nua2; // nua2 for cycle search 2/3  
	//================== bands 3 and gangster band 3 analysis
	int nband3;
	int   tcolok[2], ncolok;

	int ngua6_7, c1, c2, band, floors, digp, i81;
	uint64_t wua0, ua;// partial gua ua to check
	uint64_t tuacheck[100], tua_for_check[500];
	uint32_t uadigs_for_check[500], nua_for_check, nua_check;

	//================================= functions
	void GetStartB2(int i); // one of the 20 starts 
	void Start(int mode = 0);
	void NewBand1(int iw);
	int F17Novalid1_2();
	void Find_band2B();
	int ValidBand2();
	void ValidInitGang();
	void Find_band3B(int m10 = 1);;
	void OutEntry();
	int F3B_See_NED1();// pass p2a   
	int F3B_See_NED2();// pass p2b   
	int F3B_See_NED3();// pass 1   
	int NED2_Build_Check_Morphs();
	int NED3_Build_Check_Morphs();

	//============= loops control for UAs 5;6;7 digits collection (collect more=
	int iband, ibox, iminirow, ibox2, iminirow2, pat1, pat2, ncells;
	int tcells[6], tcols[6];
	int bcols[2][9], mycols[9], myfloors;
	uint64_t mybf;
};


// main process 
// limits for tables of UAs
#define MAX6 300
#define MAX7 200
#define MAX8 200
#define MAX9 100
#define MAX10 50
#define MAXMORE 200

struct G17B {// hosting the search in 6 6 5 mode combining bands solutions
	G17B();// initial tasks all commands
	BF128 p17diag;// for regressive test on known
	uint64_t pk54,pk54n;

	int b3lim,	 aigstop, aigstopxy,nb3_not_found,knownt,
		npuz, a_17_found_here ;
	int  b1maxcl, b2maxcl, b2maxcl11;
	int ng2,ng3;
	int grid0[81];

	//____gangsters, brute force,sockets setup
	//_________________ gangster 
	int gang[9][3]; // gangcols expanded (buildgang ) 3 digits
	int* gang27; // redefines gang[9][3] as 27 integer
	int   gang_digits_cols[9][3];// active cols for a given digit

	//______sockets common to  all bands 3  
	BF128 gsock2, gsock3;
	//============================ b12 expand tables 
	uint64_t tu6[MAX6], tu7[MAX7],tu8[MAX8],tu9[MAX9], tu10[MAX10],
		tumore[MAXMORE];
	uint32_t ntu6, ntu7, ntu8, ntu9, ntu10, ntumore;// nsizec;//
	//============================ b12 no more uas to test
	BF128 dvect[2];
	uint64_t ua_ret7p, myb12, myandall,	myac,
		anduab12,build9done, tcluesxpdone,
		clean_valid_done,critical_done;
	BF128 v0_t[12], v1_t[12],vb_t[3][UABNBLOCS]
		, vc_t[3][UABNBLOCS];
	uint64_t ua_t[12], bf_clt[12], ac_clt[12], and_t[12];
	uint32_t cl_t[12];
	uint64_t and_6, and_7,and_8, and_9, and_10, min_disjoint, or_disjoint,and_disjoint;
	uint32_t	tcluesxp[20],// to access guam
		 tc_7_9[5],// 5 for expand 7 11 
		tc_10_12[3];
	int ncluesxp, ntc_6_9;


	//============  go band3
	int nclgo, nmiss;
	int  ncluesb12, ncluesb3, mincluesb3;
	uint32_t anduab3;// b3 expand

	STD_B3* myband3;

	uint32_t t3o[1000], nt3o, t3ando, t3infield, t3outseen;
	uint32_t t3b[200], nt3b, t3c[100], nt3c;// after 3/6 clues
	uint32_t t3more[200], nt3more;
	uint32_t ntoassb3;

	inline void AddT3o(uint32_t u) {
		if (nt3o >= 1000)return;
		t3o[nt3o++] = u; 
		t3ando &= u;
	}
	int SortT3o(uint32_t active=0);
	void BuildSortT3b();
	inline uint32_t GetAndT3o() {
		uint32_t wa = BIT_SET_27;
		for (uint32_t i = 0; i < nt3o; i++)
			wa &= t3o[i];
		return wa;
	}
	
	//=====================process for a new band 2 / set of bands 3
	void Start();// standard entry
	void StartInit();// initial task gangster set up 
	void UaCollector();
	inline void Adduab12(uint32_t digs, uint32_t nd);
	void FirstUasCollect();
	void SecondUasCollect();
	void UasCollect4box();
	void UasCollect6_7();

	void StartAfterUasHarvest();
	void Guas2Collect();
	void Guas2CollectG2();
	void Guas2CollectG3();
	void Guas2CollectG3_4d();
	void Guas2CollectG3_5d();

	int IsValid7pbf(uint64_t bf);
	int Debugk(int ncl, int opt = 0);
	void Expand1();
	void Expand2();
	void Expand3();
	void Expand4();
	void Expand5();
	void Expand6();
	void Expand7();
	void Expand7crit(uint64_t ac0);
	void Expand8();
	void Expand8crit(uint64_t ac0);
	void Expand9();

	void Expand_7();
	void Expand_8();
	void Valid7();
	void Valid8();
	void Valid9();
	void Valid10();
	void Expand_9_to_10();
	void Expand_9_to_11();
	void Expand_10_to_11();

	void Do7x() {
		if (!tcluesxpdone) {
			tcluesxpdone = 1;
			register uint64_t F = myb12 & ~bf_clt[5]; // cells 6 to x
			ncluesxp = 0;
			register int cell;// build table of cells 
			while (bitscanforward64(cell, F)) {
				F ^= (uint64_t)1 << cell;
				tcluesxp[ncluesxp++] = cell;
			}
		}
	}


	void GoCallB3Com();
	uint32_t IsValidB3(uint32_t bf,int debug=0);
	int IsValid_myb12();	
	

	inline int VerifyValidb3() {
		if (clean_valid_done == 2) return 1;
		if (clean_valid_done) return 0;
		clean_valid_done = 1;
		if (!IsValid_myb12()) return 0;
		clean_valid_done = 2;
		return 1;
	}


	int Valid3_1_3(uint32_t bf);
	int Valid3mm(uint32_t bf);
	void GoSubcritToMiss0(uint32_t bf, uint32_t ac);
	void GoD0F(uint32_t bf);//end all clues there
	void GoEndAll(uint32_t bf, uint32_t ac,int debug=0);
	void TryMiss1Subcritical();


	void GoB3Expand_1_3(uint32_t bf, uint32_t ac, int debug = 0);
	void GoB3Expand_4_x(SP3 spe, int debug = 0);

	void Out17(uint32_t bfb3);

};