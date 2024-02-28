/*
123456789456789123789132465
241375698375698214698214357
517863942834921576962547831;
.23..........8.1..7.9......
...3...9..........6...1....
51..6.......9...7.....4..3.;23;133;6*/

G17B::G17B() {
	memset(this, 0, sizeof(*this));
	gang27 = gang[0];
	aigstop = 0;
	// Init SGUAs tables load permanent data
	int tpcol[3][2] = { {1,2},{0,2},{0,1} };
	for (int ist = 0; ist < 3; ist++) {//stack
		for (int ircol = 0; ircol < 3; ircol++) {//first column
			int* p = tpcol[ircol], dcol = 3 * ist;
			for (int irdig = 0; irdig < 3; irdig++) {//digit1
				for (int irdig2 = 0; irdig2 < 3; irdig2++) {//digit 2
					int i = 27 * ist + 9 * ircol + 3 * irdig + irdig2;
					SGUA2& w = tsgua2[i];
					w.i_81 = i; w.i9= dcol + ircol;
					w.col1 = dcol + p[0];		w.col2 = dcol + p[1];
					w.id1 = irdig + 3 * w.col1;
					w.id2 = irdig2 + 3 * w.col2;
				}
			}
		}
	}
	for (int ist = 0; ist < 3; ist++) {//stack
		for (int irdig1 = 0; irdig1 < 3; irdig1++) {//digit1
			for (int irdig2 = 0; irdig2 < 3; irdig2++) {//digit 2
				for (int irdig3 = 0; irdig3 < 3; irdig3++) {//digit 2
					int i = 27 * ist + 9 * irdig1 + 3 * irdig2 + irdig3;
					SGUA3& w = tsgua3[i];
					w.i_81 = i;
					w.stack = ist;
					w.col1 = 3 * ist;// minirow first column in gangster
					// pointers to gangster digits
					w.id1 = 9 * ist+irdig1;
					w.id2 = 9 * ist + 3+irdig2;
					w.id3 = 9 * ist + 6 + irdig3;
					if (0) {
						cout << "sgua3 " << w.i_81 << " col1=" << w.col1 + 1
							<< " id1;id2,id3 " << w.id1
							<< ";" << w.id2 << ";" << w.id3 << endl;
					}
				}
			}
		}
	}
}

/* 17 mode pass split

566 656  pass2a
665      pass2b
773      pass2b


*/

void G17B::StartInit() {
	b1maxcl = b2maxcl = 7; b2maxcl11 = 6;
	if (op.p1)b1maxcl = b2maxcl = 6;
	else if (op.p2b) { b2maxcl11 = 5; }
	memcpy(grid0, genb12.grid0, sizeof grid0);// use first b3
	memcpy(&grid0[54], genb12.bands3[0].band0, sizeof genb12.bands3[0].band0);
	zh2b_g.Init_g0(grid0);// init brute force bands 1+2
	if (op.p1)mincluesb3 = 7;
	else mincluesb3 = 6;
	for (int i = 0; i < 9; i++) {// 9 cols to build out of gangcols
		int istack = C_box[i];
		int* d = gang[i], c = genb12.gangcols[i];
		uint32_t bit;
		bitscanforward(bit, c);
		c ^= (1 << bit);
		d[0] = bit;
		gang_digits_cols[bit][istack] = i;
		bitscanforward(bit, c);
		c ^= (1 << bit);
		d[1] = bit;
		gang_digits_cols[bit][istack] = i;
		bitscanforward(bit, c);
		d[2] = bit;
		gang_digits_cols[bit][istack] = i;
	}

	//finish sguas2/3 set up with the gangster 
	gsock2.SetAll_0();  gsock3.SetAll_0(); 
	int tpcol[3][2] = { {1,2},{0,2},{0,1} };
	for (register int ist = 0,i=0,stack=07007007; ist < 3; ist++,stack<<=3) {
		//cout << Char27out(stack) << endl;
		for (register int irst = 0; irst < 27; irst++, i++) {//stack
			{//________________________ guas2
				SGUA2& w = tsgua2[i];
				w.dig1 = gang27[w.id1];
				w.dig2 = gang27[w.id2];
				w.digs = (1 << w.dig1) | (1 << w.dig2);
				w.valid = 0;
				for (register int ib3 = 0; ib3 < genb12.nband3; ib3++) {
					STD_B3& b3 = genb12.bands3[ib3];
					register uint32_t Bf = b3.dpat[w.dig1] | b3.dpat[w.dig2],
						Bfs = Bf & stack,
						Bfc = (Bf | (Bf >> 9) | (Bf >> 18)) & 0777;// colummn pattern

					uint32_t c1, c2, r1, r2;
					bitscanforward(c1, Bfs);	bitscanreverse(c2, Bfs);
					r1 = c1/9; r2 = c2 / 9;
					if (r1 == r2) {// socket 2
						gsock2.setBit(i);
						w.valid = 1;
						b3.g.gsocket2.setBit(i);
						b3.g.pat2[i] = Bfs;
						int imini = 3 * r1 + ist, mask = 7 << (3 * imini);
						b3.g.ua2_imini[i] = imini;
						int bit27 = mask ^ Bfs, i27;
						bitscanforward(i27, bit27);
						b3.g.ua2bit27[i] = bit27;
						b3.i_27_to_81[i27] = i;
						b3.i_81_to_27[i] = i27;
						b3.g.pat2_27[i27] = Bfs;
						continue;
					}
					// can be a 4/6
					int ncol = _popcnt32(Bfc);
					if (ncol > 5) continue;
					if (ncol == 4) {// this is a ua6
						b3.g.gsocket6.setBit(i);
						gsock2.setBit(i);
						b3.g.pat2[i] = Bf;
						continue;
					}
					// 5 column find the ua4
					for (int is2 = 0,mask=7, st2 = 07007007; is2 < 3; is2++,mask<<=3,st2<<=3)
						if (is2 != ist) 		if (_popcnt32(mask & Bfc) != 1)Bf &= ~st2;
					// must also be 2 rows 
					int maskr = 0777 << (9 * r1) | 0777 << (9 * r2);
					if (Bf & ~maskr) continue;
					b3.g.gsocket4.setBit(i);
					gsock2.setBit(i);
					b3.g.pat2[i] = Bf;

				}
			}
			
			
			{ //________________________ guas3

				SGUA3& w = tsgua3[i];
				w.dig1 = gang27[w.id1];
				w.dig2 = gang27[w.id2];
				w.dig3 = gang27[w.id3];
				w.digs = 1 << w.dig1 | 1 << w.dig2 | 1 << w.dig3;
				w.valid = 0;
				for (register int ib3 = 0; ib3 < genb12.nband3; ib3++) {
					STD_B3& b3 = genb12.bands3[ib3];
					register uint32_t Bf = b3.dpat[w.dig1]
						| b3.dpat[w.dig2] | b3.dpat[w.dig3];// colummn pattern
					Bf &= stack;
					int nr = 0,  irow=0;
					if (Bf & 0777) { nr++;  irow =0; }// row1
					if (Bf & 0777000) { nr++;  irow = 1; }
					if (Bf & 0777000000) { nr++;  irow = 2; }
					if (nr == 1) {// we have a gua3
						gsock3.setBit(i);
						w.valid = 1;
						b3.g.gsocket3.setBit(i);
						b3.g.pat3[i] = Bf;
						int imini = 3 * irow + ist;
						b3.g.ua3_imini[i] = imini;
						b3.i_9_to_81[imini] = i;
					}
				}
			}
		}
	}
	for (register int ib3 = 0; ib3 < genb12.nband3; ib3++) {
		STD_B3& b3 = genb12.bands3[ib3];
		b3.g.gsocket2all = b3.g.gsocket2 | (b3.g.gsocket4 | b3.g.gsocket6);
		memset(b3.isg2, 0, sizeof b3.isg2);
		memset(b3.isg3, 0, sizeof b3.isg3);
		for (int i = 0; i < 81; i++) {
			if (b3.g.gsocket2all.On(i)) {
				if (b3.g.gsocket2.On(i))b3.isg2[i] = 2;
				else if (b3.g.gsocket4.On(i))b3.isg2[i] = 4;
				else b3.isg2[i] = 6;
			}
			if (b3.g.gsocket3.On(i))b3.isg3[i] = 1;
		}
	}
}
void G17B::Start() {// processing an entry 
	if (aigstop)return;
	p_cpt2g[0] ++;
	p_cpt2g[1] += genb12.nband3;
	nb3_not_found = genb12.nband3;
	if (op.ton || op.opcode==10 ) {
		cout << myband2.band << " nband3=" << genb12.nband3 <<" slice "<< (genb12.nb12>>6) << endl;
		if (op.ton > 1 || op.opcode == 10) {
			for (int i = 0; i < genb12.nband3; i++)
				cout << genb12.bands3[i].band << " " << i << endl;
		}
	}
	StartInit();// do all preliminary setups
	UaCollector();//_do uas/guas2_3 initial harvest
	StartAfterUasHarvest();
}


struct EXTUAS {// get a sorted subset of uas for next "collect" step
	uint64_t  t2[300];
	uint32_t  nt2;
	void GetSortB(uint64_t* t, uint32_t n, uint64_t filter, uint32_t nold = 0) {
		BF128 vsize[25][4];
		uint64_t  t2a[512];
		uint32_t  nt2a = 0;
		nt2 = nold;
		register uint64_t Fn = (~filter) & BIT_SET_2X, w;
		memset(vsize, 0, sizeof vsize);
		for (uint32_t iua = 0; iua < tuasb12.nua; iua++) {
			w = tuasb12.tua[iua];
			uint64_t cc = w >> 59;
			w &= BIT_SET_2X;
			if (!(w & Fn)) {
				int bloc = nt2a >> 7, ir = nt2a - (bloc << 7);
				vsize[cc][bloc].setBit(ir);
				t2a[nt2a++] = w;// clean the count 
			}
			if (nt2a >= 512)break;
		}
		//cout << nt2a << " nt2a" << endl;
		uint32_t nbl64 = (nt2a + 63) >> 6, x;
		for (int i1 = 4; i1 < 25; i1++) {
			uint64_t* tb64 = vsize[i1]->bf.u64;
			for (uint32_t i2 = 0; i2 < nbl64; i2++) if (tb64[i2]) {
				register uint64_t V = tb64[i2];
				while (bitscanforward64(x, V)) {// switch to 54 mode here
					V ^= (uint64_t)1 << x;
					t2[nt2++] = t2a[x + (i2 << 6)];
					if (nt2 >= 100)return;

				}
			}
		}


	}
	void GetSortA(uint64_t filter, uint32_t nold = 0) {
		nt2 = nold;
		register uint64_t Fn = (~filter) & BIT_SET_2X, w;
		for (uint32_t iua = 0; iua < tuasb12.nua; iua++) {
			w = tuasb12.tua[iua];
			if (!(w & Fn))t2[nt2++] = w;
			if (nt2 >= 100)break;
		}
		if (nt2) {
			if (nt2 > 1)
				for (uint32_t i = 0; i < nt2 - 1; i++) {
					register uint64_t Ri = t2[i];
					for (uint32_t j = i + 1; j < nt2; j++) {
						register uint64_t  Rj = t2[j];
						if ((Ri >> 59) > (Rj >> 59)) { // smaller size first 
							t2[i] = Rj; t2[j] = Ri; Ri = Rj;
						}
					}
				}
			for (uint32_t i = 0; i < nt2; i++)
				t2[i] &= BIT_SET_2X;// clean the count

		}
	}
}extuas;

void G17B::UaCollector() {
	zh2gxn.SetupFsol(grid0);
	zh2b[0].InitBands12(grid0);
	zh2gxn.InitKnown(extuas.t2, &extuas.nt2);
	tuasb12.nua = 0;
	FirstUasCollect();// uas 2 digits bands and stacks
	SecondUasCollect();// uas 345 bands 1+2
	UasCollect6_7();
	Guas2Collect();
	UasCollect4box();// 4 box in bands 1+2
	zh2b[0].InitBands12(grid0);// restore 
	//________________________________ insert stack known uas 
	STD_B3 bw;
	BANDMINLEX::PERM pp;

	for (int ib3 = 0; ib3 < genb12.nband3; ib3++) {
		STD_B3& mb3 = genb12.bands3[ib3];
		memcpy(&grid0[54], mb3.band0, sizeof genb12.bands3[0].band0);
		int grid_diag[81];
		char ze[81];
		for (int i = 0; i < 81; i++)grid_diag[C_transpose_d[i]] = grid0[i];
		for (int i = 0; i < 81; i++)  ze[i] = grid_diag[i] + '1';
		for (int istack = 0; istack < 3; istack++) {
			int ir = bandminlex.Getmin(&grid_diag[27 * istack], &pp, 0);
			if (ir < 0) {//would be bug} 
				cout << "look for stack bad return" << endl;
				return;
			}
			bw.InitBand2_3(pp.i416, &ze[27 * istack], pp, istack);
			for (uint32_t i = 0; i < bw.nua; i++) {
				BF128 wd; wd.SetAll_0();// 3x mode to build guam
				uint32_t  zed = 0, ua = bw.tua[i]&BIT_SET_27,ccua=_popcnt32(ua);
				for (uint32_t j = 0; j < 27; j++) {
					if (ua & (1 << j)) {
						int cell = C_transpose_d[j + 27 * istack];
						wd.Set_c(cell);
					}
				}
				int cc3 =  _popcnt32  (wd.bf.u32[2]);
				if (cc3 > 3) {
					if(cc3==4)	mb3.Addm4(wd);
					else mb3.Addmm(wd);
				}
				else if(cc3==2  &&  ccua>10) { // must build g2
					int i81=mb3.GetI81_2(wd.bf.u32[2]);
					guah.tg2[i81].AddIf(wd.bf.u64[0]);
				}
				else if (cc3 == 3  &&  ccua>9) { // must build g3
					int i81 = mb3.GetI81_3(wd.bf.u32[2]);
					guah.tg3[i81].AddIf(wd.bf.u64[0]);
				}
			}
		}
	}
}

inline void G17B::Adduab12( uint32_t digs, uint32_t nd) {

	uint64_t* t = zh2gxn.tua;
	uint32_t n = zh2gxn.nua,n2=0;
	BF128 tw[100];
	for (uint32_t i = 0; i < n; i++) {
		register uint64_t w = t[i], cc = _popcnt64(w);
		if (cc < 25) {	
			BF128 x; x.bf.u64[0] =  w; x.bf.u64[1] = cc;	
			tw[n2++] = x;
		}
	}
	if (n2 > 1) {// sort to check redundancy
		for (uint32_t i = 0; i < n2 - 1; i++) {
			for (uint32_t j=i+1; j < n2 ; j++) {
				if (tw[i].bf.u64[1] > tw[j].bf.u64[1]) {
					BF128 x = tw[i]; tw[i] = tw[j]; tw[j] = x;
				}
			}
		}
	}
	for (uint32_t i = 0; i < n2; i++) {
		BF128 x = tw[i];
		register uint64_t cc = x.bf.u64[1],
			w= x.bf.u64[0],nw=~w;

		if (i) {
			for (uint32_t j = 0; j < i; j++) {
				BF128 y = tw[j];
				register uint64_t ycc = y.bf.u64[1];
				if (ycc == cc) break;
				if(! (y.bf.u64[0] & nw)) { cc = 0; break; }
			}
			if (!cc)continue;// subset found
		}
		if (cc > 15) cc = 15;
		w |= (cc << 59);
		if (tuasb12.nua < UA12SIZE)tuasb12.AddInit(w, digs, nd);
	}

}
void G17B::FirstUasCollect() {// produce all uas 2/3 digits

	struct TUAS81 {// used to collect uas 2 digits
		BF128 	tall[200];// first collect
		uint32_t ntall;// , ntold;
		int Add(BF128 w, uint32_t floor) {
			uint32_t cc = w.Count96(), nfloor = ~floor;
			for (uint32_t iua = 0; iua < ntall; iua++) {
				BF128 wt = tall[iua];
				uint32_t cct = wt.bf.u32[3] >> 16;
				uint32_t floort = wt.bf.u32[3] & 0777;
				wt.bf.u32[3] = 0;
				if (cct <= cc)continue; 
				// insert here and check super set
				for (uint32_t jua = ntall; jua > iua; jua--)
					tall[jua] = tall[jua - 1];
				tall[iua] = w;// new inserted
				tall[iua].bf.u32[3] = floor | (cc << 16);
				ntall++;
				return 2;
			}
			w.bf.u32[3] = floor | (cc << 16);
			tall[ntall++] = w;// new added
			return 1;
		}
	}tuas81;
	for (int i = 0; i < 36; i++) {
		uint32_t myf = floors_2d[i];
		zh2_2[0].GoZ2D(myf);
		if (zh2gxn.nua) {
			for (uint32_t i = 0; i < zh2gxn.nua; i++) {
				register uint64_t w = zh2gxn.tua[i], cc = _popcnt64(w);
			if (cc > 15)cc = 15;
			w |= cc << 59;
			tuasb12.AddInit(w, myf, 2);
			}
		}
	}
	for (int ib3 = 0; ib3 < genb12.nband3; ib3++) {
		STD_B3& mb3 = genb12.bands3[ib3];
		memcpy(&grid0[54], mb3.band0, sizeof genb12.bands3[0].band0);
		zhgxn.SetupFsol(grid0);
		for (int i = 0; i < 36; i++) {
			uint32_t myf = floors_2d[i];
			zhou2[0].GoZ2(myf);
			if (zhgxn.nua == 1) {// this is a 18 cells 12+6
				BF128 w = zhgxn.tua[0];
				register uint32_t C = w.bf.u32[2];
				uint32_t  ncol = _popcnt32((C | (C >> 9) | (C >> 18)) & 0777);
				if (ncol != 4)  mb3.Addmm(w); 
			}
			else {
				for (uint32_t j = 0; j < zhgxn.nua; j++) {
					BF128 w = zhgxn.tua[j];
					int cc = w.Count();
					int aig = 1;// check for subsets
					if (cc == 18)continue; // has a subset
					for (uint32_t k = 0; k < zhgxn.nua; k++) if (k != j) {
						BF128 w2 = zhgxn.tua[k];
						if (w2.isSubsetOf(w)) { aig = 0; break; }
					}
					if (aig) {
						uint64_t w1 = w.bf.u64[0], cc = _popcnt64(w1);
						register uint32_t C = w.bf.u32[2];
						uint32_t cc2 = _popcnt32(C),
							ncol = _popcnt32((C | (C >> 9) | (C >> 18)) & 0777),
							nplug = 2 * ncol - cc2;
						if ((!cc) || (!cc2)) continue;//ua bands 1+2 or ua band 3
						if (nplug > 2) { 
							if(cc2==4)mb3.Addm4(w); 
							else mb3.Addmm(w);
							continue; 
						}
					}
				}
			}		
		}
	}
}
void G17B::SecondUasCollect() {// collect 345 digits in bands 1+2
	for (int i = 0; i < 84; i++) {// look for 3 digits
		uint32_t myf = floors_3d[i];
		int ir = zh2_3[0].GoZ3(myf);// cells unsolved count
		if (ir < 6) continue;// minimum for a fresh ua 3 digits
		uint64_t F = zh2_3[0].cells_unsolved.bf.u64;
		extuas.GetSortA(F);
		zh2_3[0].DoZ3Go();
		if (zh2gxn.nua) Adduab12(myf,3);
	}
	for (int i = 0; i < 126; i++) {// look for 4 digits
		int ir = zh2_4[0].GoZ4(floors_4d[i]);
		if (ir < 8) continue;// minimum for a fresh ua 4 digits
		uint64_t F = zh2gxn.unsolved_field;
		extuas.GetSortA(F);
		zh2_4[0].DoZ4Go();
		if (zh2gxn.nua) Adduab12(floors_4d[i],4);
	}
	for (int i = 0; i < 126; i++) {// look for 5 digits
		uint32_t myf = 0777 ^ floors_4d[i];
		int ir = zh2_5[0].GoZ5(myf);
		uint64_t F = zh2gxn.unsolved_field;
		extuas.GetSortB(tuasb12.tua, tuasb12.nua, F);
		zh2_5[0].DoZ5Go();
		if (zh2gxn.nua) Adduab12(myf, 5);
	}
}
void G17B::UasCollect6_7() {
	for (int i = 0; i < 84; i++) {
		uint32_t ass= floors_3d[i], myf = 0777^ass;
		uint64_t bf = zh2gxn.Getsol(ass);
		uint64_t F = bf^BIT_SET_2X;
		extuas.GetSortB(tuasb12.tua, tuasb12.nua, F);
		zh2b[0].InitBf(bf);
		zh2b[0].Dob();
		if (zh2gxn.nua) Adduab12(myf, 6);
	}
}
void G17B::UasCollect4box() {
	//___________________ box 1245
	{
		uint64_t stack = units3xBM[5].u64[0], b4 = BIT_SET_2X & (~stack);
		extuas.GetSortB(tuasb12.tua, tuasb12.nua, b4);
		zh2b[0].InitBf(stack);
	}
	zh2b[0].Dob(22);
	if (zh2gxn.nua) {
		for (uint32_t i = 0; i < zh2gxn.nua; i++) {
			register uint64_t w = zh2gxn.tua[i], cc = _popcnt64(w);	
			if (tuasb12.nua < 2550)tuasb12.AddInit(w | (cc << 59), 0,0);
		}
	}
	
	//___________________ box 1346
	{
		uint64_t stack = units3xBM[4].u64[0], b4 = BIT_SET_2X & (~stack);
		extuas.GetSortB(tuasb12.tua, tuasb12.nua,b4);
		zh2b[0].InitBf(stack);
	}
	zh2b[0].Dob(22);
	if (zh2gxn.nua) {
		for (uint32_t i = 0; i < zh2gxn.nua; i++) {
			register uint64_t w = zh2gxn.tua[i], cc = _popcnt64(w);
			if (tuasb12.nua < UA12SIZE)tuasb12.AddInit(w | (cc << 59), 0,0);
		}
	}
	//___________________ box 2356
	{
		uint64_t stack = units3xBM[5].u64[0], b4 = BIT_SET_2X & (~stack);
		extuas.GetSortB(tuasb12.tua, tuasb12.nua, b4);
		zh2b[0].InitBf(stack);
	}
	zh2b[0].Dob(22);
	if (zh2gxn.nua) {
		for (uint32_t i = 0; i < zh2gxn.nua; i++) {
			register uint64_t w = zh2gxn.tua[i], cc = _popcnt64(w);	
			if (tuasb12.nua < UA12SIZE)tuasb12.AddInit(w | (cc << 59), 0,0);
		}
	}
}

struct TTT1 {//tuab12;tua <=12 per size, then per floor
#define NB 3
	uint64_t tua0[NB*128], tua[NB * 128];
	uint32_t nua, tdigs0[NB * 128], tdigs[NB * 128],nbl;
	BF128 vs [9][NB] ;// vectors size 4/12
	struct VF {
		BF128 v2[36][NB], v3[84][NB], v4[126][NB], v5[126][NB], v6[84][NB];
	}vf;
	void Init(uint64_t* tu, uint32_t* td, uint32_t n) {
		memset(vs, 0, sizeof vs);
		nua = 0;
		for (uint32_t i = 0; i < n; i++) {
			register uint64_t U = tu[i],cc=U>>59;
			if (cc>=4 && cc <= 12) {
				tua0[nua] = U & BIT_SET_2X;
				tdigs0[nua] = td[i];
				uint32_t bloc = nua / 128, ir = nua - 128 * bloc;
				vs[cc-4][bloc].setBit(ir);
				nua++;
				if (nua >= NB * 128) break;// overflow control
			}
		}
		// copy per size 
		nbl = (nua + 63) / 64;
		uint32_t x, n2 = 0;
		for (int i = 0; i < 9; i++) {// size 4/12
			uint64_t* v = vs[i][0].bf.u64;
			for (uint32_t j = 0; j < nbl; j++) {// uas for this size
				uint64_t V = v[j];
				while (bitscanforward64(x, V)) {
					V ^= (uint64_t)1 << x;
					register uint32_t ii = x + 64 * j;
					tua[n2] = tua0[ii]  ;
					tdigs[n2++] = tdigs0[ii];
				}
			}
		}
		// build vectors per floor
		memset(&vf, 0, sizeof vf);
		for (int i = 0; i < 36; i++) {// ______________2 digits
			register uint32_t fl = floors_2d[i];
			BF128* pv = vf.v2[i];
			for (uint32_t j = 0; j < nua; j++)
				if (tdigs[j] == fl) {
					uint32_t bloc =j/ 128, ir = j - 128 * bloc;
					pv[bloc].setBit(ir);
				}
		}
		for (int i = 0; i < 84; i++) {// ______________3 digits
			register uint32_t fl = floors_3d[i],fln=~fl;
			BF128* pv = vf.v3[i];
			for (uint32_t j = 0; j < nua; j++)
				if (tdigs[j] == fl) {
					uint32_t bloc = j / 128, ir = j - 128 * bloc;
					pv[bloc].setBit(ir);
				}
			for (int i = 0; i < 36; i++) {// subset___2 digits
				uint32_t fl2 = floors_2d[i];
				if (fl2 & fln) continue;
				BF128* pv2 = vf.v2[i];
				for (uint32_t k = 0; k < nbl; k++) pv[k] |= pv2[k];
			}
		}
		for (int i = 0; i < 126; i++) {// ______________4 digits
			register uint32_t fl = floors_4d[i], fln = ~fl;
			BF128* pv = vf.v4[i];
			for (uint32_t j = 0; j < nua; j++)
				if (tdigs[j] == fl) {
					uint32_t bloc = j / 128, ir = j - 128 * bloc;
					pv[bloc].setBit(ir);
				}
			for (int i = 0; i < 84; i++) {// subset___3 digits
				uint32_t fl2 = floors_3d[i];
				if (fl2 & fln) continue;
				BF128* pv2 = vf.v3[i];
				for (uint32_t k = 0; k < nbl; k++) pv[k] |= pv2[k];
			}
		}
		for (int i = 0; i < 126; i++) {// ______________5 digits
			register uint32_t fl = 0777^floors_4d[i], fln = ~fl;
			BF128* pv = vf.v5[i];
			for (uint32_t j = 0; j < nua; j++)
				if (tdigs[j] == fl) {
					uint32_t bloc = j / 128, ir = j - 128 * bloc;
					pv[bloc].setBit(ir);
				}
			for (int i = 0; i < 126; i++) {// subset___4 digits
				uint32_t fl2 = floors_4d[i];
				if (fl2 & fln) continue;
				BF128* pv2 = vf.v4[i];
				for (uint32_t k = 0; k < nbl; k++) pv[k] |= pv2[k];
			}
		}
		for (int i = 0; i < 84; i++) {// ______________6 digits
			register uint32_t fl = 0777 ^ floors_3d[i], fln = ~fl;
			BF128* pv = vf.v6[i];
			for (uint32_t j = 0; j < nua; j++)
				if (tdigs[j] == fl) {
					uint32_t bloc = j / 128, ir = j - 128 * bloc;
					pv[bloc].setBit(ir);
				}
			for (int i = 0; i < 126; i++) {// subset___5 digits
				uint32_t fl2 = 0777^floors_4d[i];
				if (fl2 & fln) continue;
				BF128* pv2 = vf.v5[i];
				for (uint32_t k = 0; k < nbl; k++) pv[k] |= pv2[k];
			}
		}
	}
	int Load(uint64_t* td, int iv, int ix) {
		BF128* v;
		switch (iv) {
		case 2: v = vf.v2[ix]; break;
		case 3: v = vf.v3[ix]; break;
		case 4: v = vf.v4[ix]; break;
		case 5: v = vf.v5[ix]; break;
		case 6: v = vf.v6[ix]; break;
		default: return 0;
		}
		int n = 0,x;
		uint64_t* pv = v->bf.u64;
		for (uint32_t i = 0; i < nbl; i++) {
			uint64_t V = pv[i];
			while (bitscanforward64(x, V)) {
				V ^= (uint64_t)1 << x;
				register uint32_t ii = x + 64 * i;
				td[n++] = tua[ii];
			}
		}
		return n;
	}
}ttt1;


void G17B::Guas2Collect() {
	ttt1.Init(tuasb12.tua, tuasb12.tdigs, tuasb12.nua);
	guah.Init();

	for (int i81 = 0; i81 < 81; i81++) if (gsock2.On(i81)) {// initial gua2s 4 cells
		SGUA2 w = tsgua2[i81];
		uint64_t bf = zh2b_g.fd_sols[0][w.dig1].bf.u64;
		bf |= zh2b_g.fd_sols[0][w.dig2].bf.u64;
		uint64_t bf2 = units3xBM[9 + w.col1].u64[0];
		bf2 |= units3xBM[9 + w.col2].u64[0];
		bf &= bf2;
		int xcell1, xcell2;
		bitscanforward64(xcell1, bf);
		bitscanreverse64(xcell2, bf);
		int cell1=From_128_To_81[xcell1], cell2= From_128_To_81[xcell2];
		int r1 = C_row[cell1], r2 = C_row[cell2];
		if (r1 == r2) guah.Add2(bf, i81);		
	}
	Guas2CollectG2();
	Guas2CollectG3();

}
void G17B::Guas2CollectG2() {
	//___ find guas2 2 digits
	for (int i81 = 0; i81 < 81; i81++) if (gsock2.On(i81)) {
		if (guah.IsUa4(i81)) continue;// nothing to do
		SGUA2 w = tsgua2[i81];
		GUAH::GUA& gt = guah.tg2[i81];
		int i = 0;
		for (i; i < 36; i++)if (floors_2d[i] == w.digs) break;
		extuas.nt2 = ttt1.Load(extuas.t2, 2, i);

		int ir = zh2_2[0].GoZ2G2(w.digs, w.col1, w.dig1, w.col2, w.dig2);
		if (ir < 0)continue; // locked
		if (ir == 1) {//	solved)
			uint64_t U = zh2gxn.tua[0], cc = _popcnt64(U);
			guah.Add2(U, i81);
		}
		uint64_t F = zh2gxn.unsolved_field;
		zh2_2[0].DoZ2Go();
		if (zh2gxn.nua)
			for (uint32_t i = 0; i < zh2gxn.nua; i++) {
				uint64_t U = zh2gxn.tua[i];
				guah.Add2(U, i81);
			}
	}
	guah.SortClean();
	//___ find guas2 3 digits

	for (int i81 = 0; i81 < 81; i81++) if (gsock2.On(i81)) {
		if (guah.IsUa4(i81)) continue;// nothing to do
		SGUA2 w = tsgua2[i81];
		GUAH::GUA& gt = guah.tg2[i81];
		for (int i = 0; i < 84; i++) {// find UAs 3 digits
			int fl = floors_3d[i];
			if (!((fl & w.digs) == w.digs)) continue;
			uint64_t isfl = 0;// cells ok of the floors
			for (int i2 = 0, bit = 1; i2 < 9; i2++, bit <<= 1)
				if (fl & bit)	isfl |= zh2gxn.fsol[i2];
			extuas.nt2=gt.Load(extuas.t2, isfl);
			zh2gxn.nkguas = extuas.nt2;
			uint32_t istart = extuas.nt2;
			extuas.nt2 += ttt1.Load(&extuas.t2[istart], 3, i);
			int ir = zh2_3[0].GoZ3G2(fl, w.col1, w.dig1, w.col2, w.dig2),ir2;
			if (ir < 0)continue; // locked
			if (ir == 1) {//	solved)
				if (zh2gxn.nua) {
					uint64_t U = zh2gxn.tua[0];
					guah.Add2(U, i81);
				}
				continue;
			}
			ir2 = zh2_3[0].DoZ3Go();
			if (ir2 < 0) continue;
			if (zh2gxn.nua)
				for (uint32_t i = 0; i < zh2gxn.nua; i++) {
					uint64_t U = zh2gxn.tua[i];
					guah.Add2(U, i81);
				}
		}
	}// end 3 digits
	//___ find guas2 4 digits
	guah.SortClean();

	for (int i81 = 0; i81 < 81; i81++) if (gsock2.On(i81)) {
		if (guah.IsUa4(i81)) continue;// nothing to do
		SGUA2 w = tsgua2[i81];
		GUAH::GUA& gt = guah.tg2[i81];
		for (int i = 0; i < 126; i++) { 
			int fl = floors_4d[i];
			if (!((fl & w.digs) == w.digs)) continue;
			uint64_t isfl = 0;// cells ok of the floors
			for (int i2 = 0, bit = 1; i2 < 9; i2++, bit <<= 1)
				if (fl & bit)	isfl |= zh2gxn.fsol[i2];
			extuas.nt2 = gt.Load(extuas.t2, isfl);
			zh2gxn.nkguas = extuas.nt2;
			uint32_t istart = extuas.nt2;
			extuas.nt2 += ttt1.Load(&extuas.t2[istart], 3, i);
			int ir = zh2_4[0].GoZ4G2(fl, w.col1, w.dig1, w.col2, w.dig2), ir2;
			if (ir < 0)continue; // locked
			if (ir == 1) {//	solved)
				if (zh2gxn.nua) {
					uint64_t U = zh2gxn.tua[0];
					guah.Add2(U, i81);
				}
				continue;
			}
			ir2 = zh2_4[0].DoZ4Go();
			if (ir2 < 0) continue;
			if (zh2gxn.nua)
				for (uint32_t i = 0; i < zh2gxn.nua; i++) {
					uint64_t U = zh2gxn.tua[i];
					guah.Add2(U, i81);
				}
		}
	}// end 4 digits
	guah.SortClean();//60?

	//___ find guas2 5 digits

	for (int i81 = 0; i81 < 81; i81++) if (gsock2.On(i81)) {
		if (guah.IsUa4(i81)) continue;// nothing to do
		SGUA2 w = tsgua2[i81];
		GUAH::GUA& gt = guah.tg2[i81];
		for (int i = 0; i < 126; i++) { 
			int fl =0777^ floors_4d[i];
			if (!((fl & w.digs) == w.digs)) continue;
			uint64_t isfl = 0;// cells ok of the floors
			for (int i2 = 0, bit = 1; i2 < 9; i2++, bit <<= 1)
				if (fl & bit)	isfl |= zh2gxn.fsol[i2];
			extuas.nt2 = gt.Load(extuas.t2, isfl);
			//if (diag2 == 2)extuas.Dump();
			zh2gxn.nkguas = extuas.nt2;
			uint32_t istart = extuas.nt2;
			extuas.nt2 += ttt1.Load(&extuas.t2[istart], 3, i);
			int ir = zh2_5[0].GoZ5G2(fl, w.col1, w.dig1, w.col2, w.dig2), ir2;
			if (ir < 0)continue; // locked
			if (ir == 1) {//	solved)
				if (zh2gxn.nua) {
					uint64_t U = zh2gxn.tua[0];
					guah.Add2(U, i81);
				}
				continue;
			}
			ir2 = zh2_5[0].DoZ5Go();
			if (ir2 < 0) continue;
			if (zh2gxn.nua)
				for (uint32_t i = 0; i < zh2gxn.nua; i++) {
					uint64_t U = zh2gxn.tua[i];
					guah.Add2(U, i81);
				}
		}
	}// end 5 digits
	guah.SortClean(); //80?
}
void G17B::Guas2CollectG3() {
	for (int i81 = 0; i81 < 81; i81++) if (gsock3.On(i81)) {
		SGUA3 w = tsgua3[i81];
		GUAH::GUA& gt = guah.tg3[i81];

		// Setup the perms for gangsters in minirow
		int bita = 1 << w.dig1, bitb = 1 << w.dig2, bitc = 1 << w.dig3,
			digs = w.digs,triplet_perms[2][3];

		int* p = triplet_perms[0];// for per abc -> bca
		p[0] = bita | bitb; p[1] = bitb | bitc; p[2] = bitc | bita;

		p = triplet_perms[1];// for per abc -> cab
		p[0] = bita | bitc; p[1] = bitb | bita; p[2] = bitc | bitb;
		int tp3f[2][3] = { {1,2,0},{2,0,1} };// perms no valid digit
		for (int ip = 0; ip < 2; ip++) {
			// build revised gangster
			int rgangcols[9];// revised gangster
			memcpy(rgangcols, zh2gxn.gangsters, sizeof rgangcols);
			p = triplet_perms[ip];
			int c1 = w.col1, c2 = c1 + 1, c3 = c1 + 2;
			rgangcols[c1] ^= p[0];
			rgangcols[c2] ^= p[1];
			rgangcols[c3] ^= p[2];
			int i = 0;
			for (i; i < 84; i++)if (floors_3d[i] == w.digs) break;
			extuas.nt2 = ttt1.Load(extuas.t2, 3, i);
			// find UAs 3 digits one 3 digits 
			int ir= zh2_3[0].GoZ3G3(w.digs, rgangcols ),ir2;
			if (ir < 0)continue; // locked
			if (ir == 1) {//	solved)
				if (zh2gxn.nua) {
					uint64_t U = zh2gxn.tua[0];
					guah.Add3(U, i81);
				}
				continue;
			}
			ir2 = zh2_3[0].DoZ3Go();
			if (ir2 < 0) continue;
			if (zh2gxn.nua)
				for (uint32_t i = 0; i < zh2gxn.nua; i++) {
					uint64_t U = zh2gxn.tua[i];
					guah.Add3(U, i81);
				}
		}
	}
	Guas2CollectG3_4d();
}
void G17B::Guas2CollectG3_4d() {
	for (int i81 = 0; i81 < 81; i81++) if (gsock3.On(i81)) {
		SGUA3 w = tsgua3[i81];
		GUAH::GUA& gt = guah.tg3[i81];
		if (guah.IsUamin(i81)) continue;// nothing to do

		// Setup the perms for gangsters in minirow
		int bita = 1 << w.dig1, bitb = 1 << w.dig2, bitc = 1 << w.dig3,
			digs = w.digs, triplet_perms[2][3];

		int* p = triplet_perms[0];// for per abc -> bca
		p[0] = bita | bitb; p[1] = bitb | bitc; p[2] = bitc | bita;

		p = triplet_perms[1];// for per abc -> cab
		p[0] = bita | bitc; p[1] = bitb | bita; p[2] = bitc | bitb;
		int tp3f[2][3] = { {1,2,0},{2,0,1} };// perms no valid digit
		for (int ip = 0; ip < 2; ip++) {
			// build revised gangster
			int rgangcols[9];// revised gangster
			memcpy(rgangcols, zh2gxn.gangsters, sizeof rgangcols);
			p = triplet_perms[ip];
			int c1 = w.col1, c2 = c1 + 1, c3 = c1 + 2;
			rgangcols[c1] ^= p[0];
			rgangcols[c2] ^= p[1];
			rgangcols[c3] ^= p[2];
			for (int i = 0; i < 126; i++) {
				int fl = floors_4d[i];
				if (!((fl & w.digs) == w.digs)) continue;
				uint64_t isfl = 0;// cells ok of the floors
				for (int i2 = 0, bit = 1; i2 < 9; i2++, bit <<= 1)
					if (fl & bit)	isfl |= zh2gxn.fsol[i2];
				extuas.nt2 = gt.Load(extuas.t2, isfl);
				zh2gxn.nkguas = extuas.nt2;
				uint32_t istart = extuas.nt2;
				extuas.nt2 += ttt1.Load(&extuas.t2[istart], 4, i);
				int ir = zh2_4[0].GoZ4G3(fl, rgangcols), ir2;
				if (ir < 0)continue; // locked
				if (ir == 1) {//	solved)
					if (zh2gxn.nua) {
						uint64_t U = zh2gxn.tua[0];
						if (_popcnt64(U) < 18) guah.Add3(U, i81);						
					}
					continue;
				}
				ir2 = zh2_4[0].DoZ4Go();
				if (ir2 < 0) continue;
				if (zh2gxn.nua)
					for (uint32_t i = 0; i < zh2gxn.nua; i++) {
						uint64_t U = zh2gxn.tua[i];
						if (_popcnt64(U) < 18) 
							guah.Add3(U, i81);						
					}
			}
		}
	}
	guah.SortClean3();
	Guas2CollectG3_5d();
}
void G17B::Guas2CollectG3_5d() {
	for (int i81 = 0; i81 < 81; i81++) if (gsock3.On(i81)) {
		SGUA3 w = tsgua3[i81];
		GUAH::GUA& gt = guah.tg3[i81];
		if (guah.IsUamin(i81)) continue;// nothing to do
		if (gt.nua >= 10) continue;

		// Setup the perms for gangsters in minirow
		int bita = 1 << w.dig1, bitb = 1 << w.dig2, bitc = 1 << w.dig3,
			digs = w.digs, triplet_perms[2][3];

		int* p = triplet_perms[0];// for per abc -> bca
		p[0] = bita | bitb; p[1] = bitb | bitc; p[2] = bitc | bita;

		p = triplet_perms[1];// for per abc -> cab
		p[0] = bita | bitc; p[1] = bitb | bita; p[2] = bitc | bitb;
		int tp3f[2][3] = { {1,2,0},{2,0,1} };// perms no valid digit
		for (int ip = 0; ip < 2; ip++) {
			// build revised gangster
			int rgangcols[9];// revised gangster
			memcpy(rgangcols, zh2gxn.gangsters, sizeof rgangcols);
			p = triplet_perms[ip];
			int c1 = w.col1, c2 = c1 + 1, c3 = c1 + 2;
			rgangcols[c1] ^= p[0];
			rgangcols[c2] ^= p[1];
			rgangcols[c3] ^= p[2];
			for (int i = 0; i < 126; i++) {
				int fl = 0777^floors_4d[i];
				if (!((fl & w.digs) == w.digs)) continue;
				uint64_t isfl = 0;// cells ok of the floors
				for (int i2 = 0, bit = 1; i2 < 9; i2++, bit <<= 1)
					if (fl & bit)	isfl |= zh2gxn.fsol[i2];
				extuas.nt2 = gt.Load(extuas.t2, isfl);
				zh2gxn.nkguas = extuas.nt2;
				uint32_t istart = extuas.nt2;
				extuas.nt2 += ttt1.Load(&extuas.t2[istart], 5, i);
				int ir = zh2_5[0].GoZ5G3(fl, rgangcols), ir2;
				if (ir < 0)continue; // locked
				if (ir == 1) {//	solved)
					if (zh2gxn.nua) {
						uint64_t U = zh2gxn.tua[0];
						if (_popcnt64(U) < 18) 
							guah.Add3(U, i81);						
					}
					continue;
				}

				ir2 = zh2_5[0].DoZ5Go();
				if (ir2 < 0) continue;
				if (zh2gxn.nua)
					for (uint32_t i = 0; i < zh2gxn.nua; i++) {
						uint64_t U = zh2gxn.tua[i];
						if (_popcnt64(U) < 18) guah.Add3(U, i81);						
					}
			}
		}
	}
	guah.SortClean3();
}
//__________ end of initial uas harvest switch to 54 mode
void G17B::StartAfterUasHarvest() {
	guah54n.Build();
	t54b12.Build_ta128(tuasb12.tua, tuasb12.nua);
	if (op.ton > 3)
	//if (op.f4)
		t54b12.DebugA();

	//Expand_03();
	Expand1();
}


void GUAH54N::Z128::EnterFresh(uint64_t u) {
	if (n >= 128) return;
	t[n] = u;
	uint32_t nr = n++;
	killer &= u;
	v0.setBit(nr);
	if(u&g17b.bf_clt[5])	v6.clearBit(nr);// free if hit
	if (u & g17b.bf_clt[8])v9.clearBit(nr); 
	register uint32_t cell;
	register uint64_t U = u;
	while (bitscanforward64(cell, U)) {
		U ^= (uint64_t)1 << cell;
		vc[cell].clearBit(nr);
	}
}
void GUAH54N::Build() {// cut to 30 switch to 54 killer
	Init();
	for (int i81 = 0; i81 < 81; i81++) {
		if (g17b.gsock2.On(i81)) {
			GUAH::GUA& g0 = guah.tg2[i81];
			uint32_t n = g0.nua;
			if (0 && n == 1) {
				register uint64_t U = g0.tua[0];
				U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
				BLOC0& b0 = bloc0[nbl0++];
				b0.ua = U; b0.id = i81;
				continue;
			}
			indg2[i81] = nzzused;
			Z128& myz = zz[nzzused++];
			myz.Init(0, i81);
			for (uint32_t i = 0; i < n; i++) {
				register uint64_t U = g0.tua[i];
				//if (n > 30 && nn > 16) break;
				U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
				myz.EnterInit(U);
			}
		}
	}
	nzzg2= nzzused;
	for (int i81 = 0; i81 < 81; i81++) {
		if (g17b.gsock3.On(i81)) {
			GUAH::GUA& g0 = guah.tg3[i81];
			uint32_t n = g0.nua;
			if (0 && n == 1) {
				register uint64_t U = g0.tua[0];
				U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
				//cout << "using bloc0 for " << nbl0 << endl;
				BLOC0& b0 = bloc0[nbl0++];
				b0.ua = U; b0.id = i81+100;
				continue;
			}
			indg3[i81] = nzzused;
			Z128& myz = zz[nzzused++];
			myz.Init(1, i81);
			for (uint32_t i = 0; i < n; i++) {
				register uint64_t U = g0.tua[i];
				U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
				myz.EnterInit(U);
			}
		}
	}
}
void GUAH54N::Build3() {
	for (uint32_t i = 0; i < nzzused; i++) {
		Z128& myz = zz[i];
		myz.v3 = myz.vc[g17b.cl_t[0]]& myz.vc[g17b.cl_t[1]] & myz.vc[g17b.cl_t[2]];
	}
}
void GUAH54N::Build6() {
	for (uint32_t i = 0; i < nzzused; i++) {
		Z128& myz = zz[i];
		myz.v6=myz.v3& myz.vc[g17b.cl_t[3]] & myz.vc[g17b.cl_t[4]] & myz.vc[g17b.cl_t[5]];
	}
}
void GUAH54N::Build9() {
	for (uint32_t i = 0; i < nzzused; i++) {
		Z128& myz = zz[i];
		myz.v9 = myz.v6 & myz.vc[g17b.cl_t[6]] & myz.vc[g17b.cl_t[7]] & myz.vc[g17b.cl_t[8]];
	}
}
int PackSort( uint64_t* tin, uint32_t& ntin) {
	uint64_t t[20][100], nt[15];
	memset(nt, 0, sizeof nt);
	for (uint32_t j = 0; j < ntin; j++) {
		register uint64_t R = tin[j];
		if (!R)return 1; //dead
		register uint64_t cc = _popcnt64(R);
		if (cc > 14)cc = 14;
		t[cc][nt[cc]++] = R;
	}
	ntin = 0;
	{	//check redundancy
		for (uint32_t i = 1; i <= 14; i++) {
			for (uint32_t j = 0; j < nt[i]; j++) {
				register uint64_t R = t[i][j], nR = ~R;
				for (uint32_t k = 0; k < ntin; k++)
					if (!(tin[k] & nR)) { R = 0; break; }
				if (R) tin[ntin++] = R;

			}
		}
	}
	return 0;
}

inline void GUAH54N::AddBuildlast(int ix) {
	if (ix >= 100) {// this is a g3
		ix -= 100;	g3l.setBit(ix);	tg3[ntg3l++] = ix;
	}
	else { g2l.setBit(ix);		tg2[ntg2l++] = ix; }
}
inline void GUAH54N::AddBuildGet(int ix) {
	if (ix >= 100) {// this is a g3
		ix -= 100; if (g3.On(ix))return;
		g3.setBit(ix);	tg3[ntg3++] = ix;
	}
	else {
		if (g2.On(ix))return;
		g2.setBit(ix);		tg2[ntg2++] = ix;
	}
}
inline void GUAH54N::AddBuildGet2(int ix,int mode) {
	if (mode) {// this is a g3
		if (g3.On(ix))return;
		g3.setBit(ix);	tg3[ntg3++] = ix;
	}
	else {
		if (g2.On(ix))return;
		g2.setBit(ix);		tg2[ntg2++] = ix;
	}
}
void GUAH54N::Build9last() {// switch to one table 9clues for 10
	int locdiag = 0;
	//if (p_cpt2g[60] == 49) locdiag = 1;
	uint32_t* tc = &g17b.cl_t[6];
	if (locdiag) {
		cout << "entry Build9last() "<< tc[0]<<" " << tc[1]<<" " << tc[2] 
			<<" nbl0=" << nbl0<<  "  nzzused="<< nzzused  << endl;
		cout << Char54out(g17b.ac_clt[8]) << " ac for buildlast" << endl;
	}
	ngtul = ntg2l = ntg3l = 0;
	g2l.SetAll_0(); g3l = g2l;

	for (uint32_t i = 0; i < nbl0; i++) {
		register uint64_t U = bloc0[i].ua, id = bloc0[i].id;
		if (U & g17b.bf_clt[8]) continue;
		U&& g17b.ac_clt[8];
		if (!U) { AddBuildlast((int)id);	continue; }
		gtul[ngtul++] = U | id << 54;

	}
	for (uint32_t i = 0; i < nzzused; i++) {
		Z128& myz = zz[i];
		if (locdiag ) {
			if ((myz.v6& myz.v0).isNotEmpty()) {
				cout << "dump mode " << myz.mode2_3 << " i81" << myz.i81 << endl;
				(myz.v6 & myz.v0).Print(" v6");
			}
		}
		if (myz.killer & g17b.bf_clt[8]) continue;
		BF128 v = myz.v6 & myz.v0 & myz.vc[tc[0]] & myz.vc[tc[1]] & myz.vc[tc[2]];
		if (locdiag ) v.Print(" v");
		if ((v).isEmpty()) continue;
		uint64_t id = myz.i81 + 100 * myz.mode2_3, idor = id << 54;
		uint64_t tt[128];		uint32_t  ntt = 0;
		{
			int x;
			//uint32_t rngtu = ngtul;
			while ((x = v.getFirst128()) >= 0) {
				v.Clear(x);
				register uint64_t U = myz.t[x] & g17b.ac_clt[8];
				if (!U) { AddBuildlast((int)id); ntt = 0; break; } // will never bit hit later
				tt[ntt++] = U;
			}
			if ( ntt) {
				//Table54Dump(tt, ntt);
				PackSort(tt, ntt);
				//cout << "after pack" << endl;
				//Table54Dump(tt, ntt);
				for (uint32_t j = 0; j < ntt; j++)
					if(ngtul< GTULSIZE)gtul[ngtul++] = tt[j] | idor;
			}
		}
	}
	p_cpt2g[44] += g2l.Count();

	if (locdiag) {
		cout << "exit Build9last() ngtul=" << ngtul << " ntg2l = " << ntg2l
			<< " ntg3l = " << ntg3l << endl;
		Dumpgtul(1);
	}
}
void GUAH54N::Build10last() {// switch to one table 9clues for 10
	uint32_t c1=g17b.cl_t[9];
	ngtul = ntg2l = ntg3l = 0;
	g2l.SetAll_0(); g3l = g2l;

	for (uint32_t i = 0; i < nbl0; i++) {
		register uint64_t U = bloc0[i].ua, id = bloc0[i].id;
		if (U & g17b.bf_clt[9]) continue;
		U&& g17b.ac_clt[9];
		if (!U) { AddBuildlast((int)id);	continue; }
		gtul[ngtul++] = U | id << 54;
	}
	for (uint32_t i = 0; i < nzzused; i++) {
		Z128& myz = zz[i];
		if (myz.killer & g17b.bf_clt[9]) continue;
		BF128 v = myz.v9 & myz.v0 & myz.vc[c1] ;
		if ((v).isEmpty()) continue;
		uint64_t id = myz.i81 + 100 * myz.mode2_3, idor = id << 54;
		{
			int x, nn = v.Count();
			uint32_t rngtu = ngtul;
			while ((x = v.getFirst128()) >= 0) {
				v.Clear(x);
				register uint64_t U = myz.t[x] & g17b.ac_clt[9];
				if (!U) { AddBuildlast((int)id); ngtul = rngtu; nn = 0; break; } // will never bit hit later
				gtul[ngtul++] = U | idor;
			}
			if (p_cpt2g[43] < nn)p_cpt2g[43] = nn;// test maxi trouvé 18
		}
	}
	p_cpt2g[44] += g2l.Count();
}


void GUAH54N::GetG2G3_7() {	
	GetG2G3A(g17b.bf_clt[6]);
	for (uint32_t it = 0; it < nzzused; it++) {
		Z128& myz = zz[it];
		if (g17b.bf_clt[6] & myz.killer) continue;
		BF128 v = (myz.v6 & myz.v0) & myz.vc[g17b.cl_t[6]];
		if (v.isNotEmpty())AddBuildGet2(myz.i81, myz.mode2_3);
	}
}
void GUAH54N::GetG2G3_8() {
	GetG2G3A(g17b.bf_clt[7]);
	for (uint32_t it = 0; it < nzzused; it++) {
		Z128& myz = zz[it];
		if (g17b.bf_clt[7] & myz.killer) continue;
		BF128 v = (myz.v6 & myz.v0) & myz.vc[g17b.cl_t[6]] & myz.vc[g17b.cl_t[7]];
		if (v.isNotEmpty())AddBuildGet2(myz.i81, myz.mode2_3);
	}
}
void GUAH54N::GetG2G3_9() {
	GetG2G3A(g17b.bf_clt[8]);
	for (uint32_t it = 0; it < nzzused; it++) {
		Z128& myz = zz[it];
		if (g17b.bf_clt[8] & myz.killer) continue;
		BF128 v = (myz.v9 & myz.v0) ;
		if (v.isNotEmpty()) 
			AddBuildGet2(myz.i81, myz.mode2_3);		
	}
}
void GUAH54N::GetG2G3_10() {
	GetG2G3A(g17b.bf_clt[9]);
	for (uint32_t it = 0; it < nzzused; it++) {
		Z128& myz = zz[it];
		if (g17b.bf_clt[9] & myz.killer) continue;
		BF128 v = myz.v9 & myz.v0& myz.vc[g17b.cl_t[9]];
		if (v.isNotEmpty())AddBuildGet2(myz.i81, myz.mode2_3);
	}
}
void GUAH54N::GetG2G3_10last() {
	g2 = g2l;	g3 = g3l;	ntg2 = ntg2l; ntg3 = ntg3l;
	register uint64_t A = g17b.ac_clt[9], F = g17b.bf_clt[9];
	for (uint32_t i = 0; i < ngtul; i++) {
		register uint64_t U = gtul[i], id = U >> 54;
		if (U & F) continue;
		AddBuildGet((int)id);
	}
}
void GUAH54N::GetG2G3_11() {
	GetG2G3A(g17b.bf_clt[10]);
	for (uint32_t it = 0; it < nzzused; it++) {
		Z128& myz = zz[it];
		if (g17b.bf_clt[10] & myz.killer) continue;
		BF128 v = myz.v9 & myz.v0 & myz.vc[g17b.cl_t[9]] & myz.vc[g17b.cl_t[10]];
		if (v.isNotEmpty())AddBuildGet2(myz.i81, myz.mode2_3);
	}
}

//==========================================================
//================================  start expand UAs bands 1+2

int G17B::IsValid7pbf(uint64_t bf) {
	//if ( (op.f4 == p_cpt2g[4])) 
		cout << Char54out(bf) << " check valid " << _popcnt64(bf) << endl;;
	
	if (zh2b[1].IsValid(bf)) {
		anduab12 = ~0;
		uint64_t nn = _popcnt64(bf);
		register uint64_t ua54;
		for (uint32_t i = 1; i <= zh2gxn.nua; i++) {
			uint32_t j = zh2gxn.nua - i;
			register uint64_t ua = zh2gxn.tua[j], cc = _popcnt64(ua);
			ua54 = (ua & BIT_SET_27) | ((ua & BIT_SET_B2) >> 5);
			if(!i)ua_ret7p = ua54;// return last (smaller)
			anduab12 &= ua54;
			//if ((op.opcode == 10) || (op.f4 == p_cpt2g[4])) 
			if(op.f4){
				cout << Char54out(ua54) << "freshua nclues=" << nn << " size"
					<< _popcnt64(ua54) << endl;;
			}
			switch (nn) {
			case 10:if (ntu10 < MAX10) tu10[ntu10++] = ua54;
			case 9:if (ntu9 < MAX9) tu9[ntu9++] = ua54;
			case 8:if (ntu8 < MAX8) tu8[ntu8++] = ua54;
			case 7:if (ntu7 < MAX7) tu7[ntu7++] = ua54;
			case 6:	if (ntu6 < MAX6) tu6[ntu6++] = ua54;
				if (t54b12.nc128)t54b12.AddC(ua54 );
			}
			if (_popcnt64(ua54) < 21) { t54b12.AddB(ua54); t54b12.AddA(ua54); }

		}
		return 1;
	}
	return 0;
}

#define SKTEXA(I,J,C) \
bitscanforward64(C, p);\
register uint64_t bit = (uint64_t)1 << C;\
I.possible_cells ^= bit;\
I.active_cells ^= bit;\
J = I;\
J.all_previous_cells |= bit

#define CALLB3(I,J) \
ncluesb12 = I; ncluesb3 = J;\
GoCallB3Com();if (aigstop)return

uint64_t GetBest(uint64_t v, uint64_t* t, uint64_t ac) {
	uint64_t uar=0,n=64;
	uint32_t x,cpt=0;
	while (bitscanforward64(x, v)) {
		register uint64_t bit = (uint64_t)1 << x,
			U = t[x] & ac, n2 = _popcnt64(U);
		if (n2 < n) { uar = U; n = n2; }
		if (n2 < 4 || ++cpt>10) break;
	}
	return uar;
}
uint64_t GetBest(BF128 v, uint64_t* t, uint64_t ac) {
	if (v.bf.u64[0])		return GetBest(v.bf.u64[0], t, ac);
	else return GetBest(v.bf.u64[1], &t[64], ac);
}

int G17B::Debugk(int ncl, int opt ) {
	if (op.opcode != 10)  return 0; 
	switch (ncl) {
	case 1:
		if (bf_clt[0] & pk54n)return 1;
		cout << Char54out(bf_clt[0]) << " expected 1 clues  known " << endl;
		break;
	case 2:
		if (bf_clt[1] & pk54n)return 1;
		cout << Char54out(bf_clt[1]) << " expected 2 clues  known " << endl;
		break;
	case 3:
		if (bf_clt[2] & pk54n)return 1;
		cout << Char54out(bf_clt[2]) << " expected 3 clues known" << endl;
		break;
	case 4:
		if (bf_clt[3] & pk54n)return 1;
		cout << Char54out(bf_clt[3]) << " expected 4 clues known " << endl;
		break;
	case 5:
		if (bf_clt[4] & pk54n)return 1;
		cout << Char54out(bf_clt[4]) << " expected 5 clues known" << endl;
		break;
	case 6:
		if (bf_clt[5] & pk54n)return 1;
		cout << Char54out(bf_clt[5]) << " expected 6 clues known" << endl;
		break;
	case 7:
		if (bf_clt[6] & pk54n)return 1;
		cout << Char54out(bf_clt[6]) << " expected 7 clues known" << endl;
		break;
	case 8:
		if (bf_clt[7] & pk54n)return 1;
		cout << Char54out(bf_clt[7]) << " expected 8 clues known" << endl;
		break;
	case 9:
		if (bf_clt[8] & pk54n)return 1;
		cout << Char54out(bf_clt[8]) << " expected 9 clues known" << endl;
		if( opt==1)Table54Dump(tu9, ntu9);
		break;
	case 10:
		if (bf_clt[9] & pk54n)return 1;
		cout << Char54out(bf_clt[9]) << " expected 10 clues known" << endl;
		break;
	case 20:
		if (myb12 & pk54n)return 1;
		cout << Char54out(myb12) << " expected b12 known" << endl;
		break;
	}

	return 0;
}

inline void Ac_px_6clues(uint64_t& active, uint64_t bf) {
	uint64_t nb1 = _popcnt64(bf & BIT_SET_27);
	if (nb1 == 6 && (g17b.b1maxcl == 6))active &= ~(uint64_t)BIT_SET_27;
}
inline void Ac_px_7clues(uint64_t& active, uint64_t bf) {
	uint64_t nb1 = _popcnt64(bf & BIT_SET_27);
	if (!nb1) active &= BIT_SET_27;// 7 clues in b2
	else if (nb1 == 7) active &= ~(uint64_t)BIT_SET_27;
	else if ((nb1 == 1) && (g17b.b2maxcl == 6))  active &= BIT_SET_27;
	else if (nb1 == 6 && (g17b.b1maxcl == 6))active &= ~(uint64_t)BIT_SET_27;
}
inline void Ac_px_8clues(uint64_t& active, uint64_t bf) {
	uint64_t nb1 = _popcnt64(bf & BIT_SET_27);
	if (nb1 == 1) active &= BIT_SET_27;// 7 clues in b2
	else if (nb1 == 7) active &= ~(uint64_t)BIT_SET_27;
	else if ((nb1 == 2) && (g17b.b2maxcl == 6))  active &= BIT_SET_27;
	else if (nb1 == 6 && (g17b.b1maxcl == 6)) active &= ~(uint64_t)BIT_SET_27;
}
inline void Ac_px_9clues(uint64_t& active, uint64_t bf) {
	uint64_t nb1 = _popcnt64(bf & BIT_SET_27);
	if (nb1 == 2) active &= BIT_SET_27;// 7 clues in b2
	else if (nb1 == 7) active &= ~(uint64_t)BIT_SET_27;
	else if ((nb1 == 3) && (g17b.b2maxcl == 6))  active &= BIT_SET_27;
	else if (nb1 == 6 && (g17b.b1maxcl == 6)) active &= ~(uint64_t)BIT_SET_27;
}
inline int Ac_px_10clues(uint64_t& active, uint64_t bf) {
	uint64_t nb1 = _popcnt64(bf & BIT_SET_27), nb2 = 10 - nb1;
	if (nb1 > 6 || nb2 > g17b.b2maxcl11) return 1;// now 656 or 566
	if ((nb2 == g17b.b2maxcl11))  active &= BIT_SET_27;
	else if (nb1 == 6)active &= ~(uint64_t)BIT_SET_27;
	return 0;
}


//===================== expand shared p1 p2
int PackSortOnActive2(uint64_t bf, uint64_t active, uint64_t* tin, uint32_t ntin,
	uint64_t* tout, uint32_t& ntout, uint64_t& wand) {
	register uint64_t Ac = active, Wa = ~0;
	uint64_t t[20][100], nt[15];
	memset(nt, 0, sizeof nt);
	for (uint32_t j = 0; j < ntin; j++) {
		register uint64_t R = tin[j];
		if (R & bf) continue;
		R &= Ac;
		if (!R)return 1; //dead
		register uint64_t cc = _popcnt64(R);
		if (cc > 14)cc = 14;
		t[cc][nt[cc]++] = R;
	}
	ntout = 0;
	{	//check redundancy
		for (uint32_t i = 1; i <= 14; i++) {
			for (uint32_t j = 0; j < nt[i]; j++) {
				register uint64_t R = t[i][j], nR = ~R;
				for (uint32_t k = 0; k < ntout; k++)
					if (!(tout[k] & nR)) { R = 0; break; }
				if (R) { tout[ntout++] = R; Wa &= R; }
			}
		}
	}
	wand = Wa;
	return 0;
}
void PackGetOutActive( uint64_t active, uint64_t* tin, uint32_t ntin,uint64_t* tout, uint32_t& ntout) {
	register uint64_t nac = ~active;
	uint64_t t[20][100], nt[15];
	memset(nt, 0, sizeof nt);
	for (uint32_t j = 0; j < ntin; j++) {
		register uint64_t R = tin[j]&nac;
		if (!R ) continue;
		register uint64_t cc = _popcnt64(R);
		if (cc > 14)cc = 14;
		t[cc][nt[cc]++] = R;
	}
	ntout = 0;
	{	//check redundancy
		for (uint32_t i = 1; i <= 14; i++) {
			for (uint32_t j = 0; j < nt[i]; j++) {
				register uint64_t R = t[i][j], nR = ~R;
				for (uint32_t k = 0; k < ntout; k++)
					if (!(tout[k] & nR)) { R = 0; break; }
				if (R)  tout[ntout++] = R;
			}
		}
	}
}
int PackSortOnActive(uint64_t active, uint64_t* tin, uint32_t& ntin) {
	register uint64_t Ac = active;
	uint64_t t[20][100], nt[15];
	memset(nt, 0, sizeof nt);
	for (uint32_t j = 0; j < ntin; j++) {
		register uint64_t R = tin[j] & Ac;
		if (!R)return 1; //dead
		register uint64_t cc = _popcnt64(R);
		if (cc > 14)cc = 14;
		t[cc][nt[cc]++] = R;
	}
	ntin = 0;
	{	//check redundancy
		for (uint32_t i = 1; i <= 14; i++) {
			for (uint32_t j = 0; j < nt[i]; j++) {
				register uint64_t R = t[i][j], nR = ~R;
				for (uint32_t k = 0; k < ntin; k++)
					if (!(tin[k] & nR)) { R = 0; break; }
				if (R) tin[ntin++] = R;

			}
		}
	}
	return 0;
}
inline uint64_t PackGetAnd(uint64_t bf, uint64_t active, uint64_t* tin, uint32_t ntin) {
	register uint64_t Bf=bf,Ac = active, Wa = ~0;
	for (uint32_t j = 0; j < ntin; j++) {
		register uint64_t R = tin[j];
		if (R & Bf) continue;
		Wa &= R & Ac;
		if (!Wa)return 0; //dead
	}
	return Wa;
}


int DisjointsSize5(uint64_t& active, uint64_t* tin, uint32_t ntin, int nsizex[5], int locdiag = 0) {
	uint32_t l1 = ntin, l2 = ntin, l3 = ntin;
	register uint64_t Ac = active;
	uint64_t min_count = _popcnt64(Ac);
	for (uint32_t i1 = 0; i1 < l1; i1++) {
		g17b.min_disjoint = active;
		g17b.and_disjoint = active;
		g17b.or_disjoint = 0;
		register uint64_t U1 = tin[i1];
		for (uint32_t i2 = i1 + 1; i2 < l2; i2++) {
			register uint64_t U2 = tin[i2];
			if (U1 & U2) continue;
			register uint64_t uo2 = U1 | U2;
			nsizex[0]++;
			if (l1 > 10)l1 = 10;
			if (locdiag > 2) cout << "dis2 " << i1 << " " << i2 << endl;
			for (uint32_t i3 = i2 + 1; i3 < l3; i3++) {
				register uint64_t U3 = tin[i3];
				if (uo2 & U3) continue;
				register uint64_t uo3 = uo2 | U3;
				nsizex[1]++;
				if (l2 >15)l2 = 15;
				if (locdiag > 3) cout << "dis3 " << i1 << " " << i2 << " " << i3 << endl;
				for (uint32_t i4 = i3 + 1; i4 < ntin; i4++) {
					register uint64_t U4 = tin[i4];
					if (uo3 & U4) continue;
					register uint64_t uo4 = uo3 | U4;
					nsizex[2]++;
					if (l3 > 20)l1 = 20;
					{// check min disjoint size -1
						g17b.or_disjoint |= uo4;
						g17b.and_disjoint &= uo4;
						register uint64_t min_count2 = _popcnt64(uo4);
						if (min_count2 < min_count) {
							g17b.min_disjoint = uo4;
							min_count = min_count2;
						}

					}
					// here 5 disjoints is critical
					register uint64_t wa = ~0;
					for (uint32_t i5 = i4 + 1; i5 < ntin; i5++) {
						register uint64_t U5 = tin[i5];
						if (uo4 & U5) continue;
						wa &= U5;
						if (!wa) return 1;//dead more 5						
					}
					if (wa != ~0) {// this is a critical disjoint
						Ac &= wa | uo4;
						nsizex[3]++;
						if (locdiag) cout << "dis5 " << i1 << " " << i2 << " " << i3 << " " << i4 << endl;
						if (!Ac) return 2;
					}
				}
			}
		}
	}
	active = Ac;
	return 0;
}
int DisjointsSize4(uint64_t& active, uint64_t* tin, uint32_t ntin, int nsizex[5], int locdiag = 0) {
	uint32_t l1 = ntin, l2 = ntin, l3 = ntin;
	register uint64_t Ac = active;
	g17b.min_disjoint = active;
	g17b.and_disjoint = active;
	g17b.or_disjoint = 0;
	uint64_t min_count = _popcnt64(Ac);
	for (uint32_t i1 = 0; i1 < l1; i1++) {
		register uint64_t U1 = tin[i1];
		for (uint32_t i2 = i1 + 1; i2 < l2; i2++) {
			register uint64_t U2 = tin[i2];
			if (U1 & U2) continue;
			register uint64_t uo2 = U1 | U2;
			nsizex[0]++;
			if (l1 > 10)l1 = 10;
			//if (locdiag ) cout << " dis2 " << i1 << " " << i2 << endl;
			for (uint32_t i3 = i2 + 1; i3 < l3; i3++) {
				register uint64_t U3 = tin[i3];
				if (uo2 & U3) continue;
				register uint64_t uo3 = uo2 | U3;
				nsizex[1]++;
				if (l2 > 15)l2 = 15;
				if (locdiag ) cout << " dis3 " << i1 << " " << i2 << " " << i3 << endl;
				{// check min disjoint size -1
					g17b.or_disjoint |= uo3;
					g17b.and_disjoint &= uo3;
					register uint64_t min_count2 = _popcnt64(uo3);
					if (min_count2 < min_count) {
						g17b.min_disjoint = uo3;
						min_count = min_count2;
					}

				}
				// here 4 disjoints is critical
				register uint64_t wa = ~0;
				for (uint32_t i4 = i3 + 1; i4 < ntin; i4++) {
					register uint64_t U4 = tin[i4];
					if (uo3 & U4) continue;
					if (locdiag) cout <<Char54out(uo3|U4)
						<< " dis4 " << i1 << " " << i2 << " " << i3 << " " << i4 << endl;
					wa &= U4;
					if (!wa) return 1;//dead more 4
				}
				if (wa != ~0) {// this is a critical disjoint
					Ac &= wa | uo3;
					nsizex[2]++;
					if (!Ac) return 2;
				}				
			}
		}
	}
	active = Ac;
	return 0;
}
int DisjointsSize3(uint64_t& active, uint64_t* tin, uint32_t ntin, int nsizex[5], int locdiag = 0) {
	uint32_t l1 = ntin, l2 = ntin;
	register uint64_t Ac = active;
	g17b.min_disjoint = active;
	g17b.and_disjoint = active;
	g17b.or_disjoint = 0;
	uint64_t min_count = _popcnt64(Ac);
	for (uint32_t i1 = 0; i1 < l1; i1++) {
		register uint64_t U1 = tin[i1];
		for (uint32_t i2 = i1 + 1; i2 < l2; i2++) {
			register uint64_t U2 = tin[i2];
			if (U1 & U2) continue;
			register uint64_t uo2 = U1 | U2;
			nsizex[0]++;
			if (l1 > 10)l1 = 10;
			if (locdiag>1) cout << "dis2 " << i1 << " " << i2 << endl;
			{// check min disjoint size -1
				g17b.or_disjoint |= uo2;
				g17b.and_disjoint &= uo2;
				register uint64_t min_count2 = _popcnt64(uo2);
				if (min_count2 < min_count) {
					g17b.min_disjoint = uo2;
					min_count = min_count2;
				}

			}
			register uint64_t wa = ~0;
			for (uint32_t i3 = i2 + 1; i3 < ntin; i3++) {
				register uint64_t U3 = tin[i3];
				if (uo2 & U3) continue;
				register uint64_t uo3 = uo2 | U3;
				if (l2 > 15)l2 = 15;
				if (locdiag) cout << Char54out(uo3)
					<< "dis3 " << i1 << " " << i2 << " " << i3 << endl;
				// here 3 disjoints is critical
				wa &= U3;
				if (!wa) return 1;//dead more 3	
			}
			if (wa != ~0) {// this is a critical disjoint
				Ac &= wa | uo2;
				nsizex[1]++;
				//cout << Char54out(uo2) << " uo2" << endl;
				//cout << Char54out(wa | uo2) << " new 3 " << i1 << " " << i2 << endl;
				if (!Ac) return 2;

			}
		}
	}
	active = Ac;
	return 0;
}
int DisjointsSize2(uint64_t& active, uint64_t* tin, uint32_t ntin, int nsizex[5], int locdiag = 0) {
	uint32_t l1 = ntin-1;
	register uint64_t Ac = active;
	for (uint32_t i1 = 0; i1 < l1; i1++) {
		register uint64_t U1 = tin[i1];
		register uint64_t wa = ~0;
		for (uint32_t i2 = i1 + 1; i2 < ntin; i2++) {
			register uint64_t U2 = tin[i2];
			if (U1 & U2) continue;
			register uint64_t uo2 = U1 | U2;
			if (locdiag) cout << "dis2 " << i1 << " " << i2 << endl;
			wa &= U2;
			if (!wa) return 1;//dead  2	
			for (uint32_t i3 = i2 + 1; i3 < ntin; i3++) {
				register uint64_t U3 = tin[i3];
				if (!(uo2 & U3))return 1;// more than 2 disjoints
			}
		}
		if (wa != ~0) {// this is a critical disjoint
			Ac &= wa | U1;
			nsizex[0]++;
			if (!Ac) return 2;
		}
	}
	active = Ac;
	return 0;
}

inline uint64_t DisShrink5(uint64_t ac0, uint64_t acdis, uint64_t* tin, uint32_t& ntin, int locdiag = 0) {
	if (ac0 == acdis) return acdis;
	uint64_t ac1 = acdis;
	if (locdiag) cout << " start pack" << endl;
	while (1) {// loop till no fresh set of active cells
		if (PackSortOnActive(ac1, tin, ntin)) {
			if (locdiag) cout << "dead pack" << endl;
			return 0;// empty ua found
		}
		if (locdiag > 1)Table54Dump(tin, ntin);
		int nsize[5] = { 0,0,0,0,0 };
		if (DisjointsSize5(ac1, tin, ntin, nsize, locdiag)) {
			if (locdiag) cout << "dead disj5" << endl;
			return 0;
		}
		// here must have a critical size
		if (ac1 == acdis) {
			if (locdiag) cout << "no loop" << endl;
			return ac1;
		}
		acdis = ac1;// loop with new critical field
		if (locdiag)cout << Char54out(ac1) << " critical loop " << _popcnt64(ac1) << endl;
	}

}
inline uint64_t DisShrink4(uint64_t ac0, uint64_t acdis,uint64_t* tin, uint32_t & ntin,  int locdiag = 0) {
	if (ac0 == acdis) return acdis;
	uint64_t ac1 = acdis;
	if (locdiag) cout << " start pack" << endl;
	while (1) {// loop till no fresh set of active cells
		if (PackSortOnActive(ac1, tin, ntin)) {
			if (locdiag) cout << "dead pack" << endl;
			return 0;// empty ua found
		}
		if (locdiag > 1)Table54Dump(tin, ntin);
		int nsize[5] = { 0,0,0,0,0 };
		if (DisjointsSize4(ac1, tin, ntin, nsize, locdiag)) {
			if (locdiag) cout << "dead disj4" << endl;
			return 0;
		}
		// here must have a critical size
		if (ac1 == acdis) {
			if (locdiag) cout << "no loop" << endl;
			return ac1;
		}
		acdis = ac1;// loop with new critical field
		if (locdiag)cout << Char54out(ac1) << " critical loop " << _popcnt64(ac1) << endl;
	}

}
inline uint64_t DisShrink3(uint64_t ac0, uint64_t acdis, uint64_t* tin, uint32_t& ntin, int locdiag = 0) {
	if (ac0 == acdis) return acdis;
	uint64_t ac1 = acdis;
	if (locdiag) cout << " start pack" << endl;
	while (1) {// loop till no fresh set of active cells
		if (PackSortOnActive(ac1, tin, ntin)) {
			if (locdiag) cout << "dead pack" << endl;
			return 0;// empty ua found
		}
		if (locdiag > 1)Table54Dump(tin, ntin);
		int nsize[5] = { 0,0,0,0,0 };
		if (DisjointsSize3(ac1, tin, ntin, nsize, locdiag)) {
			if (locdiag) cout << "dead disj3" << endl;
			return 0;
		}
		// here must have a critical size
		if (ac1 == acdis) {
			if (locdiag) cout << "no loop" << endl;
			return ac1;
		}
		acdis = ac1;// loop with new critical field
		if (locdiag)cout << Char54out(ac1) << " critical loop " << _popcnt64(ac1) << endl;
	}


}
inline uint64_t DisShrink2(uint64_t ac0, uint64_t acdis, uint64_t* tin, uint32_t& ntin, int locdiag = 0) {
	if (ac0 == acdis) return acdis;
	uint64_t ac1 = acdis;
	if (locdiag) cout << " start pack" << endl;
	while (1) {// loop till no fresh set of active cells
		if (PackSortOnActive(ac1, tin, ntin)) {
			if (locdiag) cout << "dead pack" << endl;
			return 0;// empty ua found
		}
		if (locdiag > 1)Table54Dump(tin, ntin);
		int nsize[5] = { 0,0,0,0,0 };
		if (DisjointsSize2(ac1, tin, ntin, nsize, locdiag)) {
			if (locdiag) cout << "dead disj3" << endl;
			return 0;
		}
		// here must have a critical size
		if (ac1 == acdis) {
			if (locdiag) cout << "no loop" << endl;
			return ac1;
		}
		acdis = ac1;// loop with new critical field
		if (locdiag)cout << Char54out(ac1) << " critical loop " << _popcnt64(ac1) << endl;
	}


}



#define NEWCLUE(M,N) 		register uint64_t bit = (uint64_t)1 << cl_t[N];\
bf_clt[N] = bf_clt[M] | bit;ua_t[N] ^= bit;ac_clt[N] ^= bit;


struct BUILD {
	uint64_t uat[2560], uout[2000], v[25][40], ac, wand; // 2560=40*64
	uint32_t nuat, nuout, npersize[25], vpersize;
	inline void Init(uint64_t active) {
		memset(v, 0, sizeof v);
		nuat = 0; ac = active; vpersize = 0; wand = ~0;
		memset(npersize, 0, sizeof npersize);
	}
	inline void Get64(uint64_t vec, uint64_t* tin) {
		uint32_t x;
		while (bitscanforward64(x, vec)) {
			vec ^= (uint64_t)1 << x; //clear bit
			register uint64_t	U = tin[x] & ac, cc = _popcnt64(U);
			int bloc = nuat >> 6, ir = nuat - (bloc << 6);
			register uint64_t bit = (uint64_t)1 << ir;
			if (nuat < 2560) {
				if (cc > 24)cc = 24;
				uat[nuat++] = U;			v[cc][bloc] |= bit;
				npersize[cc]++;				vpersize |= 1 << cc;
			}
		}
	}
	int Get64And(uint64_t vec, uint64_t* tin) {
		uint32_t x;
		while (bitscanforward64(x, vec)) {
			vec ^= (uint64_t)1 << x; //clear bit
			wand &= tin[x] & ac;
			if (!wand) return 1;
		}
		return 0;
	}
	int Dead() { return npersize[0]; }
	int Build_uout() {
		nuout = 0;
		uint32_t x;
		while (bitscanforward(x, vpersize)) {
			vpersize ^= 1 << x; //clear bit
			uint32_t nx = npersize[x], y, ix = 0;
			uint64_t* vx = v[x], * myt = uat;
			while (1) {
				uint64_t mvx = vx[ix];
				while (bitscanforward64(y, mvx)) {
					mvx ^= (uint64_t)1 << y; //clear bit
					nx--;
					register uint64_t	U = myt[y], nu = ~U;
					// check redundancy
					for (uint32_t i = 0; i < nuout; i++)
						if (!(uout[i] & nu)) { U = 0; break; }
					if (U) uout[nuout++] = U;
				}
				if (nx && ix < 39) { ix++; myt += 64; }
				else break;
			}
		}
		return nuout;
	}
	int GetBuildC(uint64_t active, BF128* vx, uint32_t lim);
	uint64_t GetAndC(uint64_t active, BF128* vx);

	void CutToSize(uint64_t siz) {
		while (nuout > 3) {
			if (_popcnt64(uout[nuout - 1]) > siz) nuout--;
			else return;
		}
	}
	int CopyTo(uint64_t* td, uint32_t maxtd) {
		if (nuout > maxtd) {
			g17b.aigstop = 1;
			cout << " overflow in build copy" << endl;
			return 0;
		}
		memcpy(td, uout, nuout * sizeof uout[0]);
		return nuout;
	}
	void DumpOut() {
		for (uint32_t i = 0; i < nuout; i++)
			cout << Char54out(uout[i])
			<< " " << _popcnt64(uout[i]) << " build i=" << i << endl;
	}

}bbb54;
int BUILD::GetBuildC(uint64_t active, BF128* vx, uint32_t lim) {
	Init(active);
	for (uint32_t i = 0; i <= t54b12.ncblocs; i++) {// set all vectors
		T54B12::TUVECT& vv = t54b12.tc128[i];
		BF128 v = vv.v0 & vx[i];
		Get64(v.bf.u64[0], vv.t);
		Get64(v.bf.u64[1], &vv.t[64]);
		if (nuat > lim) break;
	}
	if (Dead()) return -1;
	return Build_uout();
}
uint64_t BUILD::GetAndC(uint64_t active, BF128* vx) {
	ac = active; wand = ~0;
	for (uint32_t i = 0; i <= t54b12.ncblocs; i++) {// set all vectors
		T54B12::TUVECT& vv = t54b12.tc128[i];
		BF128 v = vv.v0 & vx[i];
		if (Get64And(v.bf.u64[0], vv.t)) return 0;
		if (Get64And(v.bf.u64[1], &vv.t[64]))return 0;
	}
	return wand;
}

//_______________________ reducing tables of UAs bands 1+2
void T54B12::Build_ta128(uint64_t* t, uint32_t n) {

	// here insert all missing uas one band (1 or 2)
	for (int i = 0; i < 2; i++) {
		STD_B416& wb = (i) ? myband2 : myband1;
		BF64 wt; wt.bf.u64 = 0;
		uint32_t* tu = wb.tua, nu = wb.nua;
		for (uint32_t j = 0; j < nu; j++) {
			register uint32_t u = tu[j] & BIT_SET_27, cc = _popcnt32(u);
			wt.bf.u32[i] = u;
			if (cc > 12)if (n < UA12SIZE)t[n++] = wt.bf.u64;
		}
	}
	InitA();
	uint32_t nbl64 = (n + 63) >> 6, x;
	memset(vsize, 0, sizeof vsize);
	for (uint32_t i = 0; i < n; i++) {
		int bloc = i >> 7, ir = i - (bloc << 7);
		uint64_t cc = _popcnt64(t[i] & BIT_SET_2X);
		if (cc > 24) continue;//safety
		vsize[cc][bloc].setBit(ir);
	}
	uint32_t ntw = 0;
	for (int i1 = 4; i1 < 25; i1++) {
		uint64_t* tb64 = vsize[i1]->bf.u64;
		for (uint32_t i2 = 0; i2 < nbl64; i2++) if (tb64[i2]) {
			register uint64_t V = tb64[i2];
			while (bitscanforward64(x, V)) {// switch to 54 mode here
				V ^= (uint64_t)1 << x;
				register uint64_t R = t[x + (i2 << 6)];
				R = (R & BIT_SET_27) | ((R & BIT_SET_B2) >> 5);
				if (1) {// check redundancy and subsets
					for (uint32_t i = 0; i < ntw; i++) {
						if (!(R & (~tw[i]))) {
							R = 0; break;
						}
					}
					if (R)tw[ntw++] = R;
					else continue;
				}
				AddA(R);
			}
		}
	}
}
int T54B12::Build_tb128N() {
	uint32_t* tc = g17b.cl_t;
	uint32_t lastbloc = t54b12.nablocs;
	bbb54.Init(g17b.ac_clt[2]);// init pick up and set active 
	// first bloc ready for pick up
	bbb54.Get64(g17b.v0_t[2].bf.u64[0], ta128[0].t);
	bbb54.Get64(g17b.v0_t[2].bf.u64[1], &ta128[0].t[64]);
	// other bloc need upate of vect
	for (uint32_t i = 1; i <= lastbloc; i++) {
		TUVECT& vv = ta128[i];
		BF128 v = vv.v0 & vv.vc[tc[0]] & vv.vc[tc[1]] & vv.vc[tc[2]];
		bbb54.Get64(v.bf.u64[0], vv.t);
		bbb54.Get64(v.bf.u64[1], &vv.t[64]);
	}
	if (bbb54.Dead()) return 1;
	int nuout = bbb54.Build_uout();
	//__Build the reduced set of UAs vectors
	InitB();
	for (int i = 0; i < nuout; i++) AddB(bbb54.uout[i]);

	//if (nb128 < 128) nb128 = 128; //forcing add outside first bloc
	return 0;
}
int T54B12::Build_tc128N() {
	uint32_t* tc = &g17b.cl_t[3];
	uint32_t lastbloc = t54b12.nbblocs;
	bbb54.Init(g17b.ac_clt[5]);// init pick up and set active 
	// first bloc ready for pick up
	bbb54.Get64(g17b.v0_t[5].bf.u64[0], tb128[0].t);
	bbb54.Get64(g17b.v0_t[5].bf.u64[1], &tb128[0].t[64]);
	// other bloc need upate of vect
	for (uint32_t i = 1; i <= lastbloc; i++) {
		TUVECT& vv = tb128[i];
		BF128 v = vv.v0 & vv.vc[tc[0]] & vv.vc[tc[1]] & vv.vc[tc[2]];
		bbb54.Get64(v.bf.u64[0], vv.t);
		bbb54.Get64(v.bf.u64[1], &vv.t[64]);
	}
	if (bbb54.Dead()) return 1;
	int nuout = bbb54.Build_uout();
	//Table54Dump(bbb54.uout, nuout);
	return 0;

	//__Build the reduced set of UAs vectors
	InitB();
	int ntw = 0; // pour test
	uint32_t nbl64 = (ntw + 63) >> 6, x;
	for (int i1 = 1; i1 < 19; i1++) {
		uint64_t* tb64 = vsize[i1]->bf.u64;
		for (uint32_t i2 = 0; i2 < nbl64; i2++) if (tb64[i2]) {
			register uint64_t V = tb64[i2];
			while (bitscanforward64(x, V)) {
				V ^= (uint64_t)1 << x;
				AddB(tw[x + (i2 << 6)]);
			}
		}
	}
	if (nb128 < 128) nb128 = 128; //forcing add outside first bloc
	return 0;
}

void G17B::Expand1() {
	//t54b12.DebugA();
	if (aigstop) return;
	T54B12::TUVECT& tuv128 = t54b12.ta128[0];
	uint64_t* twu = tuv128.t;
	ac_clt[0] = BIT_SET_54;
	ua_t[0] = twu[0];
	//if (1) 	cout << Char54out(ua_t[0]) << " ua for 1" << endl;
	

	while (bitscanforward64(cl_t[0], ua_t[0])) {
		{
			register uint64_t bit = (uint64_t)1 << cl_t[0];
			bf_clt[0] = bit;
			ua_t[0] ^= bit; //clear bit
			ac_clt[0] ^= bit;
		}
		v0_t[0] = tuv128.v0 & tuv128.vc[cl_t[0]];
		if (v0_t[0].isEmpty()) {// would surely be bug
			cout << "no more ua in first 128 for clue 2" << endl;
			aigstop = 1;			return;
		}
		ua_t[1] = GetBest(v0_t[0], twu, ac_clt[0]);
		ac_clt[1] = ac_clt[0];
		Expand2();
		if (aigstop) return;
	}
}
void G17B::Expand2() {
	if (aigstop) return;
	if (Debugk(1))return;
	T54B12::TUVECT& tuv128 = t54b12.ta128[0];
	uint64_t* twu = tuv128.t;
	//if (1) 	cout <<"  " << Char54out(ua_t[1]) << " ua for 2" << endl;


	while (bitscanforward64(cl_t[1], ua_t[1])) {
		{NEWCLUE(0, 1)}
		v0_t[1] = v0_t[0] & tuv128.vc[cl_t[1]];
		if (v0_t[1].isEmpty()) {// would surely be bug
			cout << "no more ua in first 128 for clue 3" << endl;
			aigstop = 1;			return;
		}
		ua_t[2] = GetBest(v0_t[1], twu, ac_clt[1]);
		ac_clt[2] = ac_clt[1];
		Expand3();
		if (aigstop) return;
	}
}
void G17B::Expand3() {
	if (aigstop) return;
	if (Debugk(2))return;
	T54B12::TUVECT& tuv128 = t54b12.ta128[0];
	uint64_t* twu = tuv128.t;
	//if (1) 	cout<<"    " << Char54out(ua_t[2]) << " ua for 3" << endl;
	while (bitscanforward64(cl_t[2], ua_t[2])) {
		{NEWCLUE(1, 2)}
		v0_t[2] = v0_t[1] & tuv128.vc[cl_t[2]];
		if (t54b12.Build_tb128N()) continue;
		p_cpt2g[3]++;
		Expand4();
		if (aigstop) return;
	}
}
void G17B::Expand4() {
	if (Debugk(3))return;
	if (aigstop) return;
	if (op.f3 && (op.f3 < p_cpt2g[3])) { aigstop = 1; return; }
	if (0 && op.ton) {
		cout << Char54out(bf_clt[2]) << " [3]" << p_cpt2g[3] << endl;

		if (op.ton > 1)if (op.f3 == p_cpt2g[3])t54b12.DebugB();
	}
	// be sure to have room for fresh uas
	ntu6 = ntu7 = ntu8 = ntu9 = ntu10 = 0;
	t54b12.InitC();
	guah54n.Build3();

	T54B12::TUVECT& tuv128 = t54b12.tb128[0];
	uint64_t* twu = tuv128.t;
	ac_clt[3] = ac_clt[2];
	ua_t[3] = twu[0];
	//if (op.f3 && (op.f3 == p_cpt2g[3]))
	//	cout<<"\t" << Char54out(ua_t[3]) << " ua for 4" << endl;
	while (bitscanforward64(cl_t[3], ua_t[3])) {
		{NEWCLUE(2, 3)}
		for (uint32_t i = 0; i <= t54b12.nbblocs; i++)// set all vectors
			vb_t[0][i] = t54b12.tb128[i].vc[cl_t[3]];
		BF128 v = tuv128.v0 & vb_t[0][0];
		if (v.isEmpty()) {// would surely be bug
			cout << "no more ua in first 128 for clue 5" << endl;
			aigstop = 1;			return;
		}
		ua_t[4] = GetBest(v, twu, ac_clt[3]);
		ac_clt[4] = ac_clt[3];
		if (op.f3 && (op.f3 == p_cpt2g[3])) {
			cout << Char54out(bf_clt[3]) << " bf for 4" << endl;
			//cout << Char54out(ac_clt[3]) << " ac for 4" << endl;
			cout << Char54out(ua_t[4]) << " ua for 5" << endl;
		}
		p_cpt2g[50]	++;
		//if (p_cpt2g[50] == 1)
		Expand5();
		if (aigstop) return;
	}
}
void G17B::Expand5() {
	if (aigstop) return;
	if (Debugk(4))return;
	T54B12::TUVECT& tuv128 = t54b12.tb128[0];
	uint64_t* twu = tuv128.t, * twu2;
	//cout << "\t  " << Char54out(ua_t[4]) << " ua for 5" << endl;
	while (bitscanforward64(cl_t[4], ua_t[4])) {
		{NEWCLUE(3, 4)}
		for (uint32_t i = 0; i <= t54b12.nbblocs; i++)// set all vectors
			vb_t[1][i] = vb_t[0][i] & t54b12.tb128[i].vc[cl_t[4]];
		BF128 v;
		twu2 = 0;
		for (uint32_t i = 0; i <= t54b12.nbblocs; i++) {// find first v non empty
			v = t54b12.tb128[i].v0 & vb_t[1][i];
			if (v.isNotEmpty()) {
				twu2 = t54b12.tb128[i].t; break;
			}
		}
		if (!twu2) {// would surely be bug
			cout << "empty for clue 6" << endl;		aigstop = 1;	return;
		}
		ua_t[5] = GetBest(v, twu2, ac_clt[4]);
		ac_clt[5] = ac_clt[4];
		if (op.f3 && (op.f3 == p_cpt2g[3])) {
			cout << Char54out(bf_clt[4]) << " bf 5" << endl;
			//cout << Char54out(ac_clt[4]) << " ac 5" << endl<<endl;
			cout << Char54out(ua_t[5]) << " ua for 6" << endl;
		}
		p_cpt2g[51]	++;
		//if (p_cpt2g[51] == 1)
			Expand6();
		if (aigstop) return;
	}
}
void G17B::Expand6() {
	if (aigstop) return;
	if (Debugk(5))return;
	T54B12::TUVECT& tuv128 = t54b12.tb128[0];
	uint64_t* twu = tuv128.t;
	//cout << "\t    " << Char54out(ua_t[5]) << "  6 " << endl;
	while (bitscanforward64(cl_t[5], ua_t[5])) {
		{NEWCLUE(4, 5)}
		if (op.f3 && (op.f3 == p_cpt2g[3])) {
			//cout << Char54out(bf_clt[5]) << " bf 6  [4]="<< p_cpt2g[4] << endl;
			//cout << Char54out(ac_clt[5]) << " ac 6" << endl;
			//cout << Char54out(ua_t[6]) << " ua for 7" << endl;
		}

		Ac_px_6clues(ac_clt[5], bf_clt[5]);

		bbb54.Init(ac_clt[5]);// init pick up and set active
		for (uint32_t i = 0; i <= t54b12.nbblocs; i++) {// set all vectors
			T54B12::TUVECT& vv = t54b12.tb128[i];
			BF128 v = vv.v0 & vb_t[1][i] & vv.vc[cl_t[5]];
			bbb54.Get64(v.bf.u64[0], vv.t);
			bbb54.Get64(v.bf.u64[1], &vv.t[64]);
		}
		if (bbb54.Dead()) continue;
		int nuout = bbb54.Build_uout();
		if (!nuout) {//  unlikely a 6 clues to check
			cout << "empty for clue 6" << endl;		aigstop = 1;	return;
		}
		t54b12.InitC();
		for (int i = 0; i < nuout; i++) {
			register uint64_t U = bbb54.uout[i];
			t54b12.AddC(U);
		}
		p_cpt2g[4]	++;
		ntumore = 0;
		//cout << Char54out(bf_clt[5]) << "  6  [4] "<< p_cpt2g[4]
		//	<< "   [3] " << p_cpt2g[3] << endl;
		Expand7();		if (aigstop) return;
	}
}

void G17B::Expand7() {
	if (Debugk(6))return;
	if (aigstop) return;
	int locdiag = 0;
	if (op.f4 && (op.f4 < p_cpt2g[4])) { aigstop = 1; return; }
	if (op.f4 == p_cpt2g[4] && op.ton) {
		cout << Char54out(bf_clt[5]) << " [4]" << p_cpt2g[4] << endl;
		if (op.ton > 1)		
			t54b12.DebugC();
		locdiag = 1;
	}
	for (int ib3 = 0; ib3 < genb12.nband3; ib3++) 
		genb12.bands3[ib3].Set6clues(cl_t);	
	guah54n.Build6();
	//if (p_cpt2g[4]==598) guah54n.Statusv6(3);

	T54B12::TUVECT& tuv128 = t54b12.tc128[0];
	uint64_t* twu = tuv128.t;
	ac_clt[6] = ac_clt[5];
	ua_t[6] = twu[0];
	if (locdiag) cout << Char54out(ua_t[6]) << " ua for 7" << endl;
	while (bitscanforward64(cl_t[6], ua_t[6])) {
		{NEWCLUE(5, 6)}
		if (locdiag)cout << Char54out(bf_clt[6]) << " next 7 clues" << endl;
		p_cpt2g[52]	++;
		ac_clt[7] = ac_clt[6];
		Ac_px_7clues(ac_clt[7], bf_clt[6]);// apply filter 7 clues
		t54b12.AddVect7(cl_t[6], vc_t[0]);
		int nuout = bbb54.GetBuildC(ac_clt[7], vc_t[0], 50);
		if (nuout < 0) continue;	
		ntu7 = 0;
		if (!nuout) {
			cout << Char54out(bf_clt[6]) << " potential 7  clues" << endl;
			if (IsValid7pbf(bf_clt[6])) {
				Expand_8();	continue;// fresh uas are in tu7				
			}
			Valid7(); continue;// we have a valid 7			
		}
		if (locdiag) 	cout << Char54out(ac_clt[6]) << "active" << endl;
		//bbb54.DumpOut();
		bbb54.CutToSize(13);
		int nsizea[5] = { 0,0,0,0,0 };
		uint64_t ac0 = ac_clt[6];
		if (DisjointsSize3(ac0, bbb54.uout, bbb54.nuout,nsizea,locdiag)) continue;		
		if (locdiag) 	cout << Char54out(ac0) << "active end "<< nsizea[1] << endl;		
		p_cpt2g[53]	++;
		if (nsizea[1] && ac0!= ac_clt[6]) { Expand7crit(ac0); continue; }
		p_cpt2g[54]	++;
		ua_t[7] = bbb54.uout[0];
		Expand8();		if (aigstop) return;
	}
}
void G17B::Expand7crit(uint64_t ac0) {
	p_cpt2g[55]	++;
	int locdiag = 0;
	if (op.f4 == p_cpt2g[4] && op.ton) {
		cout << Char54out(bf_clt[6]) << " 7 crit "  << endl;
		locdiag = 1;
	}
	int nuout = bbb54.GetBuildC(ac0, vc_t[0], 1000);
	if (locdiag) cout << "crita" << endl;
	if (nuout < 0) return;
	int nsizea[5] = { 0,0,0,0,0 };
	uint64_t ac1 = ac0;
	if (locdiag) cout << "critb" << endl;
	if (DisjointsSize3(ac1, bbb54.uout, bbb54.nuout,nsizea)) return;
	if (locdiag) cout << "critc" << endl;
	uint64_t ac2 = DisShrink3(ac1, ac0, bbb54.uout, bbb54.nuout);
	if (!ac2) return;
	p_cpt2g[56]	++;
	if (locdiag)cout << Char54out(ac2) << " ac2 crit 7 ok [56]" << p_cpt2g[56] << endl;
	//if(ac2!=ac0)bbb54.DumpOut();
	if (locdiag)bbb54.DumpOut();
	ntu7 = bbb54.CopyTo(tu7, MAX7);
	ac_clt[7] = ac2;
	if (ntu7)Expand_8();// should always be

}

void G17B::Expand8() {
	if (Debugk(7))return;
	if (aigstop) return;
	int locdiag = 0;
	if (op.f4 == p_cpt2g[4] && op.ton) {
		cout << Char54out(bf_clt[6]) << " 7 clues"  << endl;
		cout << Char54out(ua_t[7]) << " ua for 8 clues" << endl;
		locdiag = 1;
	}
	while (bitscanforward64(cl_t[7], ua_t[7])) {
		{NEWCLUE(6, 7)}
		p_cpt2g[60]	++;
		if (locdiag)cout << Char54out(bf_clt[7]) << " 8 clues [60] "<< p_cpt2g[60] << endl;
		ac_clt[8] = ac_clt[7];
		Ac_px_8clues(ac_clt[8], bf_clt[7]);
		t54b12.AddVect(cl_t[7], vc_t[0], vc_t[1]);
		int nuout = bbb54.GetBuildC(ac_clt[8], vc_t[1], 30);
		if (nuout < 0) continue;
		ntu8 = 0;
		if (!nuout) {
			cout << Char54out(bf_clt[7]) << "potential 8 clues" << endl;
			if (IsValid7pbf(bf_clt[7])) {
				Expand_9_to_10();	continue;// fresh uas are in tu8				
			}
			Valid7(); continue;// we have a valid 8
		}
		if (locdiag) 	cout << Char54out(ac_clt[7]) << "active 8" << endl;
		//bbb54.DumpOut();		
		bbb54.CutToSize(12);
		int nsizea[5] = { 0,0,0,0,0 };
		uint64_t ac0 = ac_clt[7];
		if (DisjointsSize2(ac0, bbb54.uout, bbb54.nuout,
			nsizea,locdiag)) continue;		
		p_cpt2g[61]	++;
		if (locdiag) 	cout << Char54out(ac0) << "active end " << nsizea[0] << endl;
		if (nsizea[0] && ac0 != ac_clt[7]) { Expand8crit(ac0); continue; }
		p_cpt2g[64]	++;
		ua_t[8] = bbb54.uout[0];
		if (locdiag) {
			cout << Char54out(bf_clt[7]) << "not critical 8 [64]" << p_cpt2g[64] << endl;
			cout << Char54out(ua_t[8]) << " ua for 9"  << endl;
		}
		Expand9();		if (aigstop) return;
	}
}
void G17B::Expand8crit(uint64_t ac0) {
	p_cpt2g[62]	++;
	int locdiag = 0;
	if (op.f4 == p_cpt2g[4] && op.ton) {
		cout << Char54out(bf_clt[7]) << " bf for 8crit  nuout=" << bbb54.nuout << endl;
		cout << Char54out(ac_clt[7]) << " ac for 8" << endl;
		locdiag = 1;
	}	
	int nuout = bbb54.GetBuildC(ac0, vc_t[1], 1000);
	if (nuout<0)return;
	if(locdiag)bbb54.DumpOut();
	int nsizea[5] = { 0,0,0,0,0 };
	uint64_t ac1 = ac0;
	if (DisjointsSize2(ac1, bbb54.uout, bbb54.nuout, nsizea)) return;	
	uint64_t ac2 = DisShrink2(ac1, ac0, bbb54.uout, bbb54.nuout);
	if (!ac2) return;
	p_cpt2g[63]	++;
	if (locdiag) {
		cout << Char54out(ac2) << " ac2 critical 8 ok [63]" << p_cpt2g[63] << endl;
		bbb54.DumpOut();
	}
	ntu8 = bbb54.CopyTo(tu8, MAX8);
	ac_clt[8] = ac2;
	if(ntu8)Expand_9_to_10();
}

void G17B::Expand9() {
	if (Debugk(8))return;
	if (aigstop) return;
	int locdiag = 0;
	if (op.f4 == p_cpt2g[4] && op.ton) {
		cout << Char54out(bf_clt[7]) << " 8 clues entry expand 9" << endl;
	}

	while (bitscanforward64(cl_t[8], ua_t[8])) {
		{NEWCLUE(7, 8)}
		if (Debugk(9))return;
		p_cpt2g[70]	++;
		ac_clt[9] = ac_clt[8];
		Ac_px_9clues(ac_clt[9], bf_clt[8]);
		t54b12.AddVect(cl_t[8], vc_t[1], vc_t[2]);
		{
			//register uint64_t U = bbb54.wand;
			register uint64_t U = bbb54.GetAndC(ac_clt[9],vc_t[2]);
			if (!U ) continue;
			if (!(~U)) {// potential valid 9
				cout << Char54out(bf_clt[8]) << "no more uas potential 9 clues" << endl;
				ntu9 = 0;
				if (IsValid7pbf(bf_clt[8])) {
					// fresh uas are in tu8
					U = anduab12 & ac_clt[8];
					cout << Char54out(U) << "not 9 clues new and" << endl;
					Table54Dump(tu9, ntu9);
					if(!U )continue;
				}
				else {
					cout << "valid 9 to do" << endl;
					// we have a valid 9
					continue;
				}

			}

			ua_t[9] =U;
		}
		if (locdiag) {
			cout << Char54out(bf_clt[8]) << " 9 clues [70] "<< p_cpt2g[70] << endl;
			cout << Char54out(ac_clt[9]) << " active  for 10 " << endl;

		}
		p_cpt2g[71]	++;
		guah54n.Build9last();
		while (bitscanforward64(cl_t[9], ua_t[9])) {
			{NEWCLUE(8, 9)}
			if (Debugk(10))return;
			if (locdiag) {
				cout << Char54out(bf_clt[9]) << " 10 clues  "  << endl;
				cout << Char54out(ac_clt[9]) << " active  now " << endl;

			}
			guah54n.GetG2G3_10last();
			myb12 = bf_clt[9];
			clean_valid_done = 0;
			CALLB3(10, 7);
			if (aigstop) return;
		}
	}
}


//===================  expand after critical or check not valid
void G17B::Expand_7() {
	return;// not ready
	++p_cpt2g[12];
	p_cpt2g[13] += ntu6;
	p_cpt2g[15] += _popcnt64(ac_clt[5]);
	ua_t[6] = tu6[0];// expand first ua
	//cout << Char54out(u1) << " expand7" << endl;
	//if (op.opcode == 10) 	if (Debugk(6)) return;
	if (op.f4 == p_cpt2g[4])cout << Char54out(tu6[0]) << " next ua for 7" << endl;


	while (bitscanforward64(cl_t[6], ua_t[6])) {
		{NEWCLUE(5, 6)}
		//cout << Char54out(bf_cl7) << " expand7 bf_cl7 " << endl;

		ac_clt[6] = ac_clt[5];
		Ac_px_7clues(ac_clt[6], bf_clt[6]);// apply filter 7 clues
		if (PackSortOnActive2(bf_clt[6], ac_clt[6], tu6, ntu6, tu7, ntu7, and_7))
			continue;
		if (op.opcode == 10) 	if (Debugk(7)) continue;
		//if (and_7) Potential8(); // do it and clear bits in the table
		Expand_8();
	}
	if (op.f4 == p_cpt2g[4])cout << " back for 7" << endl;

}
void G17B::Expand_8() {
	if (Debugk(7))return;

	if (op.f4 == p_cpt2g[4])cout << Char54out(tu7[0]) << " next ua for 8" << endl;

	ua_t[7] = tu7[0];
	while (bitscanforward64(cl_t[7], ua_t[7])) {
		{NEWCLUE(6, 7)}
		if (Debugk(8)) continue;
		ac_clt[8] = ac_clt[7];
		Ac_px_8clues(ac_clt[8], bf_clt[7]);// apply filter 8 clues
		if (PackSortOnActive2(bf_clt[7], ac_clt[8], tu7, ntu7, tu8, ntu8, and_8))
			continue;
		//<<<<<<<<<<<<<< si ntu8=0 voir valid 8
		if (!ntu8) {
			// we have a valid 8
			continue;
		}

		if (op.f4 == p_cpt2g[4]) {
			cout << Char54out(bf_clt[7]) << "  8 clues" << endl;
			cout << Char54out(ac_clt[7]) << "  activ" << endl;
			Table54Dump(tu8, ntu8);
		}
/*
		if (!ntu8) {
			cout << Char54out(bf_clt[7]) << "no more uas potential 8 clues" << endl;
			ntu8 = 0;
			if (IsValid7pbf(bf_clt[7])) {
				//and_8 = anduab12 & ac_cl8;
				// fresh uas are in tu8
				continue;
			}
*/
		Expand_9_to_10();
	}
	if (op.f4 == p_cpt2g[4])cout << " back for 8" << endl;

}
void G17B::Expand_9_to_10() {
	int locdiag = 0;
	//if (p_cpt2g[7] >= 473 && p_cpt2g[7] <= 475) locdiag = 2;
	ua_t[8] = tu8[0];
	if (locdiag) {
		cout << Char54out(ua_t[8]) << " first ua expand 9 to 10" << endl;
		cout << Char54out(ac_clt[8]) << " active entry" << endl;

	}
	while (bitscanforward64(cl_t[8], ua_t[8])) {
		{NEWCLUE(7, 8)}
		if (Debugk(9))continue;
		p_cpt2g[70]	++;
		ac_clt[9] = ac_clt[8];
		Ac_px_9clues(ac_clt[9], bf_clt[8]);
		ua_t[9] = PackGetAnd(bf_clt[8], ac_clt[9], tu8, ntu8);
		if (locdiag) {
			cout << Char54out(bf_clt[8]) << "  9 clues" << endl;
			cout << Char54out(ac_clt[9]) << " active now" << endl;
			cout << Char54out(ua_t[9]) << " pack end for 10" << endl;

		}

		if (!ua_t[9])continue;// no valid 10 in this branch
		if (ua_t[9] == ~0) {
			cout << " potential valid 9" << endl;
			ntu9 = 0;
			if (IsValid7pbf(bf_clt[8])) {
				ua_t[9] = anduab12 & ac_clt[8];
			}
			else {
				cout << "  valid 9" << endl;
				// this is a valid 9
				continue;

			}
		}
		p_cpt2g[46]++;
		guah54n.Build9last();
		if (locdiag) cout << "go for 10 after build 9 last" << endl;
		while (bitscanforward64(cl_t[9], ua_t[9])) {
			{NEWCLUE(8, 9)}
			ac_clt[9] = ac_clt[8];
			guah54n.GetG2G3_10last();
			if (Debugk(10))continue;
			myb12 = bf_clt[9];
			if (locdiag) {
				cout << Char54out(bf_clt[9]) << " bf_clt[9]" << endl;
				cout << Char54out(ac_clt[9]) << " ac_clt[9]" << endl;

			}
			clean_valid_done = 0;
			CALLB3(10, 7);
		}
	}
	if (locdiag) cout << " back 9 10 crit" << endl;
}


void G17B::Valid7() {
	return; // not ready
	myb12 = bf_clt[6];
	guah54n.GetG2G3_7();// try 7
	CALLB3(7, 10);
	Ac_px_7clues(ac_clt[6], bf_clt[6]);// apply filter 8 clues
	while (bitscanforward64(cl_t[7], ac_clt[6])) {// set clue 8
		uint64_t bit = (uint64_t)1 << cl_t[6];
		ac_clt[6] ^= bit; 	bf_clt[7] = bf_clt[6] | bit;
		ac_clt[7] = ac_clt[6];		Valid8();
	}
}
void G17B::Valid8() {
	if (Debugk(8))return;
	myb12 = bf_clt[7];
	guah54n.GetG2G3_8();// try 8
	CALLB3(8, 9);
	Ac_px_8clues(ac_clt[7], bf_clt[7]);// apply filter 8 clues
	while (bitscanforward64(cl_t[8], ac_clt[7])) {// set clue 9
		uint64_t bit = (uint64_t)1 << cl_t[8];
		ac_clt[7] ^= bit; 		 bf_clt[8] = bf_clt[7] | bit;
		ac_clt[8] = ac_clt[7];	Valid9();
	}
}
void G17B::Valid9() {
	guah54n.Build9();
	myb12 = bf_clt[8];
	guah54n.GetG2G3_9();// try direct
	if (op.opcode == 10) {
		if (Debugk(9))return;
		cout << "  valid 9 clues for a known puzzle "
			<< cl_t[6]<<" " << cl_t[7] << " " << cl_t[8] << " " << endl;
		guah54n.g2.Print(" g2"); guah54n.g3.Print(" g3");
	}
	CALLB3(9, 8);
	Ac_px_9clues(ac_clt[8], bf_clt[8]);// apply filter 9 clues
	if (op.p1)guah54n.Build9last();
	while (bitscanforward64(cl_t[9], ac_clt[8])) {// set clue 10
		uint64_t bit1 = (uint64_t)1 << cl_t[9];
		ac_clt[8] ^= bit1; 		bf_clt[9] = bf_clt[8] | bit1;
		ac_clt[9] = ac_clt[8];
		if (op.opcode == 10)		if (Debugk(10))continue;		
		Valid10();
	}
}
void G17B::Valid10() {
	if (op.opcode == 10) {
		if (bf_clt[9] & pk54n)return;
		cout << " expected valid 10 clues for a known puzzle" << endl;
		cout << Char54out(bf_clt[9]) << " bf_cl10" << endl;
	}
	myb12 = bf_clt[9];
	if (op.p1) {
		guah54n.GetG2G3_10last();
		CALLB3(10, 7);		return;
	}
	guah54n.GetG2G3_10();
	CALLB3(10, 7);
	if (Ac_px_10clues(ac_clt[9], bf_clt[9])) return;
	guah54n.Build10last();
	while (bitscanforward64(cl_t[10], ac_clt[9])) {
		register uint64_t bit2 = (uint64_t)1 << cl_t[10];
		ac_clt[9] ^= bit2; ac_clt[10] = ac_clt[9];
		bf_clt[10] = bf_clt[9] | bit2;	myb12 = bf_clt[10];
		guah54n.GetG2G3_11();
		CALLB3(11, 6);
	}
}

//======================================== expand p2
void G17B::Expand_9_to_11() {
	return; // a verifier
	uint64_t u2 = tu8[0];
	while (bitscanforward64(cl_t[8], u2)) {
		{
			uint64_t bit2 = (uint64_t)1 << cl_t[8];
			bf_clt[8] = bf_clt[7] | bit2;
			u2 ^= bit2; //clear bit
			ac_clt[7] ^= bit2;
		}
		ac_clt[8] = ac_clt[7];
		Ac_px_9clues(ac_clt[8], bf_clt[8]);// apply filter 8 clues
		if (PackSortOnActive2(bf_clt[8], ac_clt[8], tu8, ntu8, tu9, ntu9, and_9))
			continue;
		Expand_10_to_11();
	}
}
void G17B::Expand_10_to_11() {
	return; // a verifier
	uint64_t u1 = tu9[0];
	while (bitscanforward64(cl_t[9], u1)) {
		{
			uint64_t bit2 = (uint64_t)1 << cl_t[9];
			bf_clt[9] = bf_clt[8] | bit2;
			u1 ^= bit2; //clear bit
			ac_clt[8] ^= bit2;
		}
		ac_clt[9] = ac_clt[8];
		Ac_px_10clues(ac_clt[9], bf_clt[9]);// apply filter 8 clues
		if (PackSortOnActive2(bf_clt[9], ac_clt[9], tu9, ntu9, tu10, ntu10, and_10))
			continue;
		if (!and_10)continue;// no valid 10 in this branch
		while (bitscanforward64(cl_t[10], and_10)) {
			uint64_t bit = (uint64_t)1 << cl_t[10];
			bf_clt[9] = bf_clt[8] | bit;
			and_10 ^= bit; //clear bit
			ac_clt[9] ^= bit;
			// is it worth checking valid here???
			// call potential valid 11
		}
	}
}




//===============================expand and go search 17 pass 2 



void G17B::GoCallB3Com() {
	if (ntumore) {
		register uint64_t F = myb12;
		for(uint32_t i=0;i<ntumore;i++)	if(! (tumore[i] & F)) return;
	}
	p_cpt2g[7]++;
	p_cpt2g[80]+= guah54n.ntg2;
	if(op.f4== p_cpt2g[4])cout << Char54out(bf_clt[9]) << " 10 clues [4] " << p_cpt2g[4]
		<< "  [7] " << p_cpt2g[7]<< " ntg2 " << guah54n.ntg2 <<" "
		<< p_cpt2g[80] << endl;

	VerifyValidb3();
	return;
	if (op.opcode == 10) cout << "entry GoCallB3Com guah54n.ntg2"<< guah54n.ntg2 << endl;
	tcluesxpdone = 0;
	guah54n.InitCom();//open the door for g2 g3 seen later 
	int tb3[512], ntb3 = 0;
	for (int ib3 = 0; ib3 < genb12.nband3; ib3++) {
		STD_B3& b3 = genb12.bands3[ib3];
		if (b3.aigskip)continue;// op first and one 18 found
		b3.ntg2_4 = b3.ntg2_6 = 0;
		p_cpt2g[23]++;

		register uint32_t  Mg2 = 0, Mg3 = 0, minc = 0,
			R1 = 0, R2 = 0, R3 = 0;
		{
			register uint32_t mini;
			for (uint32_t i = 0; i < guah54n.ntg2; i++) {
				register uint32_t i81 = guah54n.tg2[i], a;
				if ((a = b3.isg2[i81])) { 
					if (a == 2) {
						Mg2 |= b3.g.ua2bit27[i81];
						mini =1<< b3.g.ua2_imini[i81];
						R3 |= R2 & mini; R2 |= R1 & mini; R1 |= mini;
					}
					else if (a == 4)b3.tg2_4[b3.ntg2_4++] = i81;
					else b3.tg2_6[b3.ntg2_6++] = i81;
				}
			}
			minc = _popcnt32(R3) + _popcnt32(R1);
			if (minc > (uint32_t)ncluesb3) continue;
			for (uint32_t i = 0; i < guah54n.ntg3; i++) {
				register uint32_t i81 = guah54n.tg3[i];
				if (b3.isg3[i81]) 	Mg3 |= 1 << b3.g.ua3_imini[i81];
			}
			Mg3 &= (R1 ^ 0x1ff);// free mini rows
			minc += _popcnt32(Mg3);
		}
		if (op.opcode == 10) cout << " min; nclues " << minc << " " << ncluesb3<<endl;
		if (minc <= (uint32_t)ncluesb3) {
			b3.ming2_3 = R3; 			
			b3.ming2_2 = R2&~R3;
			b3.ming2_1 = R1 & ~R2;
			b3.mg3 = Mg3;
			b3.mg2 = Mg2;  
			b3.minc = minc;
			tb3[ntb3++] = ib3;
		}
	}
	if (!ntb3) return;
	p_cpt2g[24]++;
	p_cpt2g[25] += ntb3;
	
	for (int i = 0; i < ntb3; i++) 
		genb12.bands3[tb3[i]].GoA();
}

int maskminirow[9] = { 07,070,0700,07000,070000,0700000,07000000,070000000,0700000000 };

void STD_B3::GoAg23(int debug) {
	for (uint32_t i = 0; i < guah54n.ntmg2; i++) {
		register uint32_t i81 = guah54n.tmg2[i], a;
			if ((a = isg2[i81])) {
			if (a == 2) {
				register uint32_t  bitmini = 1 << g.ua2_imini[i81];
				mg2 |= g.ua2bit27[i81];
				if (bitmini & ming2_2) {
					ming2_2 ^= bitmini;
					ming2_3 |= bitmini;
				}
				else if (bitmini & ming2_1) {
					ming2_1 ^= bitmini;
					ming2_2 |= bitmini;
				}
				else ming2_1 |= bitmini;
			}
			else if (a == 4)tg2_4[ntg2_4++] = i81;
			else tg2_6[ntg2_6++] = i81;
		}
	}
	for (uint32_t i = 0; i < guah54n.ntmg3; i++) {
		register uint32_t i81 = guah54n.tmg3[i];
		if (isg3[i81]) mg3 |= 1 << g.ua3_imini[i81];
	}
	register uint32_t all = ming2_1 | ming2_2 | ming2_3;
	mg3 &= ~all;
	minc = _popcnt32(all | mg3) + _popcnt32(ming2_3);
}
void STD_B3::GoA() {
	p_cpt2g[8]++;
	if (0) {
		cout << band << " Goa   min " << minc << " [8] " << p_cpt2g[8] << endl;
		return;
	}
	g17b.nt3more = 0;
	if (op.opcode == 10) cout  << " Goa   min " << minc << endl;

	if (g17b.clean_valid_done == 2 || g17b.aigstop) return;
	memcpy(&g17b.grid0[54], band0, sizeof band0);// used in brute force
	g17b.myband3 = this;
	if (guah54n.ntmg2 | guah54n.ntmg3) {// possible change in mincout
		GoAg23();
		if ((int)minc > g17b.ncluesb3) return;
	}


	// note : this is a critical code 
	xq.Init();
	xq.nb3 = g17b.ncluesb3;
	xq.nmiss = xq.nb3 - minc;

	{
		register uint32_t  Mg2 = mg2;
		// load 2 pairs in minirow

		register uint32_t M = ming2_2, x;
		while (bitscanforward(x, M)) {
			M ^= 1 << x;
			register int mask = maskminirow[x],
				v = mask & Mg2,
				i27, bit;
			xq.t1a |= (mask ^ v);// common cell
			xq.critbf |= mask;
			bitscanforward(i27, v);
			bit = 1 << i27;
			xq.t2a[xq.n2a++] = mask ^ bit;
			bit ^= v;// other i27
			xq.t2a[xq.n2a++] = mask ^ bit;

		}
		xq.t2b3 = xq.t2a + xq.n2a;
		M = ming2_3;
		while (bitscanforward(x, M)) {
			M ^= 1 << x;
			register int i0 = 3 * x;
			xq.t2b3[xq.n2b3++] = g.pat2_27[i0++];
			xq.t2b3[xq.n2b3++] = g.pat2_27[i0++];
			xq.t2b3[xq.n2b3++] = g.pat2_27[i0];
			xq.critbf |= maskminirow[x];
		}
		xq.t2b = xq.t2b3 + xq.n2b3;// now one pair
		M = ming2_1;
		while (bitscanforward(x, M)) {
			M ^= 1 << x;
			register int mask = maskminirow[x],
				v = mask & Mg2,
				a = mask ^ v;
			xq.critbf |= a;
			xq.t2b[xq.n2b++] = a;
		}
		M = mg3;// now triplets
		while (bitscanforward(x, M)) {
			M ^= 1 << x;
			register int mask = maskminirow[x];
			xq.critbf |= mask;
			xq.t2b[xq.n2b++] = mask;
		}
	}

	if (op.opcode == 10 && op.ton>1) 	xq.Dump1(); 
	p_cpt2g[9]++;
	return;
	if (!xq.nmiss) { GoB0(); return; }
	if (xq.nmiss == 1) { GoB1(); return; }
	GoBMore1();

}

//____________________ band3 miss0 at start

uint32_t  XQ::AssignMiss0(uint32_t bf) {
	nadded++;
	register uint32_t ret = 0;
	// is it a bf3 assigned
	if (n2b3) {
		register uint32_t  n = n2b3; n2b3 = 0;
		for (uint32_t i = 0; i < n; i += 3) {
			register uint32_t wa = t2b3[i] | t2b3[i + 1] | t2b3[i + 2];
			if (!(wa & bf)) {// no hit keep it
				ret |= wa;	continue;
			}
			// push the last in n2b
			wa = t2b3[i];
			if (wa & bf) {
				wa = t2b3[i+1];
				if (wa & bf) {	wa = t2b3[i + 2];}
			}
			t2b[n2b++] =wa;	ret |= wa;	n2b3 = i;
			// reload others   n2b and exit
			for (uint32_t j = i + 3; j < n; j++) {
				ret |= t2b3[j];
				t2b3[n2b3++] = t2b3[j];
			}
			for (uint32_t j = 0; j < n2b; j++) 	ret |= t2b[j];			
			return ret;
		}
		n2b3 = n; // no hit
	}
	//bf3 hits a single clue ua assigned
	register  uint32_t n = n2b;
	n2b = 0;
	for (uint32_t i = 0; i < n; i++) {
		register uint32_t U = t2b[i];
		if (U & bf) {
			for (uint32_t j = i + 1; j < n; j++) {
				register uint32_t U = t2b[j];
				t2b[n2b++] = U;		ret |=U;
			}
			break;
		}
		else {	ret |= U; n2b++;}
	}
	return ret;// should never be
}

#define MISS0ADD \
if (F & U) continue;\
if (!(U &= A)) return ; \
if (_popcnt32(U) == 1) {F |= U;	\
A =  xq.AssignMiss0(U);}\
else xq.Addin(U)

void STD_B3::GoB0() {
	xq.SetFilters();
	{// add band 3 UA size 4
		register uint32_t F = xq.fa, A = xq.fb;
		for (uint32_t i = 0; i < nua; i++) {
			register uint32_t U = tua[i];
			if( (U>>27) > 4) { xq.iuas4 = i; break; }//
			U &= BIT_SET_27;
			MISS0ADD;
		}
		for (uint32_t i = 0; i < ntg2_4; i++) {//guas 4
			int i81 = tg2_4[i];
			register uint32_t U= g.pat2[i81];
			MISS0ADD;
		}
		for (uint32_t i = 0; i < ntg2_6; i++) {//guas 6
			int i81 = tg2_6[i];
			register uint32_t U = g.pat2[i81];
			MISS0ADD;
		}
		for (uint32_t i = xq.iuas4; i < nua; i++) {// uas b3 >4
			register uint32_t U = tua[i] & BIT_SET_27;
			MISS0ADD;
		}
		if (xq.nin) {// check fresh potential 
			while (1) {// open the door tomore than one assign
				register uint32_t Fr = F, nn = xq.nin;
				xq.nin = 0;
				for (uint32_t i = 0; i < nn; i++) {
					register uint32_t U = xq.tin[i];
					MISS0ADD;
				}
				if (Fr == F) break;;
			}
		}
		if (_popcnt32 (F) == xq.nb3) {	GoC0F(F); return;}
		GoC0(F,A);
	}
}
void STD_B3::GoC0F(uint32_t bf) {// misso all known
	register uint32_t F = bf;
	g17b.Do7x();//  expensive 4 guam

	for (uint32_t i = 0; i <= nbbgm; i++) {
		GUM64& gw = tgm64[i];
		register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
		register uint32_t r;
		while (bitscanforward64(r, V)) {
			V ^= (uint64_t)1 << r;
			if (!( gw.tb3[r] & F)) return;
		}
	}
	for (uint32_t i = 0; i <= nbbgmm; i++) {
		GUM64& gw = tgm64m[i];
		register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
		register uint32_t r;
		while (bitscanforward64(r, V)) {
			V ^= (uint64_t)1 << r;
			if (!(gw.tb3[r] & F)) return;
		}
	}
	// solution to test
	g17b.GoD0F(F);

}
void STD_B3::GoC0(uint32_t bf, uint32_t a) {
	int locdiag = 0;
	register uint32_t F = bf,A=a;
	g17b.Do7x();
	xq.BuildMiss0Redundant();
	if (locdiag) {
		cout << "goC0 no redundant" << endl;
		xq.Status();
	}
	for (uint32_t i = 0; i <= nbbgm; i++) {
		GUM64& gw = tgm64[i];
		register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
		register uint32_t r;
		while (bitscanforward64(r, V)) {
			V ^= (uint64_t)1 << r;
			register uint32_t U = gw.tb3[r];
			if (U & F) continue;;
			//cout << Char27out(U) << " u gm" << endl;;
			if (!(U &= A)) return;
			if (_popcnt32(U) == 1) {
				F |= U;
				A = xq.AssignMiss0(U);
			}
			else if (xq.AddRedundant(U))
				xq.tin[xq.nin++] = U;

		}
	}
	for (uint32_t i = 0; i <= nbbgmm; i++) {
		GUM64& gw = tgm64m[i];
		register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
		register uint32_t r;
		while (bitscanforward64(r, V)) {
			V ^= (uint64_t)1 << r;
			register uint32_t U = gw.tb3[r];
			if (U & F) continue;;
			//cout << Char27out(U) << " u gmm" << endl;;
			if (!(U &= A)) return;
			if (_popcnt32(U) == 1) {
				F |= U;
				A = xq.AssignMiss0(U);
			}
			else if (xq.AddRedundant(U))
				xq.tin[xq.nin++] = U;
		}
	}
	if (locdiag) {
		cout << Char27out(F) << "all add done" << endl;
		xq.Status();
	}
	if (xq.nin) {// check again fresh potential 
		while (1) {// open the door tomore than one assign
			register uint32_t Fr = F, nn = xq.nin;
			xq.nin = 0;
			for (uint32_t i = 0; i < nn; i++) {
				register uint32_t U = xq.tin[i];
				//cout << Char27out(U&A) << " uin to see" << endl;
				MISS0ADD;
				//cout << Char27out(F) << " F new nin" << xq.nin << endl;
				//cout << Char27out(A) << " A" << endl;

			}
			if (Fr == F) break;;
		}
	}
	if (locdiag) {
		cout <<Char27out(F)<< " F final C0" << endl;
		xq.Status();
	}
	g17b.ntoassb3 = xq.nb3- _popcnt32(F) ;
	//cout << "[8] " << p_cpt2g[8] << " minc " << minc<<" ntoass "<< ntoass << endl;
	if (g17b.ntoassb3 < 0) return; // should never be
	if (!g17b.ntoassb3) {
		if (xq.nin)return;
		g17b.GoD0F(F); 
		return; 
	}
	// must now go to expand with ordered and cleaned file
	xq.BuildMiss0Out();
	if (g17b.ntoassb3 == 1) {
		int x, u;
		if (!(u = xq.GetAndout())) return; // no single clue
		if (g17b.VerifyValidb3())return;
		if (locdiag) 	cout << Char27out(u) << " 1 to assign try this nmore ="<<g17b.nt3more << endl;
		while (bitscanforward(x, u)) {
			register int bit = 1 << x;
			u ^= bit;
			if (g17b.IsValidB3(F | bit,locdiag)) u &= g17b.anduab3;
			else g17b.Out17(F | bit);
		}
		return;
	}
	if (g17b.ntoassb3 >= 4) {		g17b.GoB3Expand_1_3(F, A);		return;	}
	memcpy(g17b.t3b, xq.tout, xq.nout * sizeof g17b.t3b[0]);
	g17b.nt3b = xq.nout;
	SP3 sp3;
	sp3.active = A;
	sp3.all_previous = F;
	g17b.GoB3Expand_4_x(sp3);
}
void G17B::GoD0F(uint32_t bf) {
	if (VerifyValidb3())return;
	if (!IsValidB3(bf))Out17(bf);
}

//____________________ band3 miss1 at start
#define MISS1ADD \
if (!(U & A)){ \
wa&=U;xq.Addout(U);}\
else xq.Addin(U)

#define MISS1ADDIF if(xq.AddRedundant(U)) \
if (!(U & A)){ \
wa&=U;xq.Addout(U);}\
else xq.Addin(U)

void STD_B3::GoB1() {
	{// add band 3 UA size 4
		register uint32_t  A = xq.critbf, wa = BIT_SET_27;
		for (uint32_t i = 0; i < nua; i++) {
			register uint32_t U = tua[i];
			if ((U >> 27) > 4) { xq.iuas4 = i; break; }//
			U &= BIT_SET_27;
			MISS1ADD;
		}
		for (uint32_t i = 0; i < ntg2_4; i++) {//guas 4
			int i81 = tg2_4[i];
			register uint32_t U = g.pat2[i81];
			MISS1ADD;
		}
		for (uint32_t i = 0; i < ntg2_6; i++) {//guas 6
			int i81 = tg2_6[i];
			register uint32_t U = g.pat2[i81];
			MISS1ADD;
		}
		for (uint32_t i = xq.iuas4; i < nua; i++) {// uas b3 >4
			register uint32_t U = tua[i] & BIT_SET_27;
			MISS1ADD;
		}
		if (!wa) return;
		if (xq.nout) {	GoB1toMiss0(wa); return; }
		g17b.Do7x();
		xq.BuildMissxRedundant();
		for (uint32_t i = 0; i <= nbbgm; i++) {
			GUM64& gw = tgm64[i];
			register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
			register uint32_t r;
			while (bitscanforward64(r, V)) {
				V ^= (uint64_t)1 << r;
				register uint32_t U = gw.tb3[r];
				MISS1ADDIF;
			}
		}
		for (uint32_t i = 0; i <= nbbgmm; i++) {
			GUM64& gw = tgm64m[i];
			register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
			register uint32_t r;
			while (bitscanforward64(r, V)) {
				V ^= (uint64_t)1 << r;
				register uint32_t U = gw.tb3[r];
				MISS1ADDIF;
			}
		}
		if (!wa) return;
		if (xq.nout) { GoB1toMiss0(wa); return; }
		//___ test global  
		if (g17b.VerifyValidb3())return;

		g17b.nt3more = 0;
		if (g17b.IsValidB3(xq.critbf)) {// not valid, new outfield
			register uint32_t U = g17b.anduab3;
			if (!U) return;
			GoB1toMiss0(U); return;
		}
		// now miss1 no out try all in
		XQ xqr = xq;
		g17b.TryMiss1Subcritical();
		xq = xqr;
		uint32_t U = BIT_SET_27 ^ xq.critbf;// dummy UA for any outfield
		GoB1toMiss0(U);
	}
}
void STD_B3::GoB1toMiss0(uint32_t wa) {
	xq.t2b[xq.n2b++] = wa;
	xq.critbf |= wa;
	xq.nmiss = 0;
	xq.nout = 0;
	xq.SetFilters();
	register uint32_t F = xq.fa, A = xq.fb;
	if (xq.nin) {// check xq.in potential 
		while (1) {// open the door tomore than one assign
			register uint32_t Fr = F, nn = xq.nin;
			xq.nin = 0;
			for (uint32_t i = 0; i < nn; i++) {
				register uint32_t U = xq.tin[i];
				MISS0ADD;
			}
			if (Fr == F) break;;
		}
	}
	if (_popcnt32(F) == xq.nb3) { GoC0F(F); return; }
	GoC0(F, A);
}
void G17B::TryMiss1Subcritical() {
	memcpy(xq.tout, xq.t2a, xq.n2a * sizeof xq.tout[0]);
	memcpy(&xq.tout[xq.n2a], xq.t2b3, xq.n2b3 * sizeof xq.tout[0]);
	memcpy(&xq.tout[xq.n2a + xq.n2b3], xq.t2b, xq.n2b * sizeof xq.tout[0]);
	xq.nout = xq.n2a + xq.n2b3 + xq.n2b;// +nin;
	register uint32_t F = 0, A = xq.critbf;

	{
		uint32_t ass = 0;// load xq.in in the limit of A
		for (uint32_t i = 0; i < xq.nin; i++) {
			register uint32_t u = xq.tin[i];
			if (F & u) continue;
			if (!(u &= A)) return;// dead
			if (_popcnt32(u) == 1)ass |= u;
			else xq.tout[xq.nout++] = u;
		}
		F |= ass; xq.fa |= ass;
		A &= ~ass; xq.fb &= ~ass;
	}
	xq.nin = 0;
	if (!F) { 
		xq.CleanOut(F, A);
		GoEndAll(F, A);
		return; 
	}
	int more = xq.SubCritMore(F);
	if (more > 1) return;
	if (_popcnt32(F) == ncluesb3) {
		if (xq.NonHitOut(F))return;
	}
	if (more) {//now miss0
		xq.SubCritMoreDo(F);
		A = xq.SubCritActive(F);
		GoSubcritToMiss0(F, A);
		return;
	}
	xq.CleanOut(F, A);
	GoEndAll(F, A);
}
void G17B::GoSubcritToMiss0(uint32_t bf, uint32_t ac) {
	xq.nmiss = 0;

	register uint32_t F = bf, A = 0;
	F |= xq.t1a;
	for (uint32_t i = 0; i < xq.n2b3; i++)
		if (!(F & xq.t2b3[i]))A |= xq.t2b3[i];

	for (uint32_t i = 0; i < xq.n2b; i++)
		if (!(F & xq.t2b[i]))A |= xq.t2b[i];

	while (1) {// open the door tomore than one assign
		register uint32_t Fr = F, nn = xq.nout;
		xq.nout = 0;
		for (uint32_t i = 0; i < nn; i++) {
			register uint32_t U = xq.tout[i];
			if (F & U) continue;
			if (!(U &= A)) return;
			if (_popcnt32(U) == 1) {
				F |= U;
				A = xq.AssignMiss0(U);
			}
			else xq.Addout(U);
		}
		if (Fr == F) break;;
	}
	if (_popcnt32(F) == xq.nb3)  GoD0F(F);
	else GoEndAll(F, A);

}


//______________________ band3 missing >1 at start

void STD_B3::GoBMore1() {
	int locdiag = 0;
	register uint32_t  A = xq.critbf, wa = BIT_SET_27;
	xq.BuildMissxRedundant();
	{// add band 3 UA size 4
		for (uint32_t i = 0; i < nua; i++) {
			register uint32_t U = tua[i];
			if ((U >> 27) > 4) { xq.iuas4 = i; break; }//
			U &= BIT_SET_27;
			MISS1ADDIF;
		}
		for (uint32_t i = 0; i < ntg2_4; i++) {//guas 4
			int i81 = tg2_4[i];
			register uint32_t U = g.pat2[i81];
			MISS1ADDIF;
		}
		for (uint32_t i = 0; i < ntg2_6; i++) {//guas 6
			int i81 = tg2_6[i];
			register uint32_t U = g.pat2[i81];
			MISS1ADDIF;
		}
		for (uint32_t i = xq.iuas4; i < nua; i++) {// uas b3 >4
			register uint32_t U = tua[i] & BIT_SET_27;
			MISS1ADDIF;
		}
	}
	g17b.Do7x();// be sure to have the list of clues
	for (uint32_t i = 0; i <= nbbgm; i++) {
		GUM64& gw = tgm64[i];
		register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
		register uint32_t r;
		while (bitscanforward64(r, V)) {
			V ^= (uint64_t)1 << r;
			register uint32_t U = gw.tb3[r];
			MISS1ADDIF;
		}
	}

	for (uint32_t i = 0; i <= nbbgmm; i++) {
		GUM64& gw = tgm64m[i];
		register uint64_t V = gw.Getv(g17b.tcluesxp, g17b.ncluesxp);
		register uint32_t r;
		while (bitscanforward64(r, V)) {
			V ^= (uint64_t)1 << r;
			register uint32_t U = gw.tb3[r];
			MISS1ADDIF;
		}
	}
	if (!xq.nout) {//go direct
		xq.BuildMissxOut();
		xq.CleanOut();
		g17b.GoEndAll(0, BIT_SET_27);
		return;
	}
	if (xq.nmiss == 2) {// exit or miss1
		if (!wa) {// try miss0 or exit 
			uint64_t x = xq.Isoutsize2();
			if (x) {GoBMoretoMiss0(x);	return;	}
		}
		GoBMoretoMiss1(1);// first as disjoint
		return;
	}
	xq.CleanOut();
	if (xq.nout<=xq.nmiss-2 || wa) {//go direct
		xq.BuildMissxOut();
		xq.CleanOut();
		g17b.GoEndAll(0, BIT_SET_27);
		return;
	}
	if (xq.nmiss == 3) {
		uint64_t x = xq.Isoutsize2();
		if (!x) {//go direct
			xq.BuildMissxOut();
			xq.CleanOut();
			g17b.GoEndAll(0, BIT_SET_27);
			return;
		}
		uint64_t y = xq.Isoutsize3();
		if (!y) {// push to miss 1
			GoBMoretoMiss1(x);	return;	}
		else {	GoBMoretoMiss0(y);	return;	}
	}
	if (xq.nmiss == 4) {
		uint64_t x = xq.Isoutsize3();
		if (!x) {//go direct
			xq.BuildMissxOut();
			g17b.GoEndAll(0, BIT_SET_27);
			return;
		}
		uint64_t y = xq.Isoutsize4();
		if (!y) {// push to miss 1
			GoBMoretoMiss1(x);	return;	}
		else {	GoBMoretoMiss0(y);	return;	}
	}
	xq.BuildMissxOut();
	g17b.GoEndAll(0, BIT_SET_27);
}
void STD_B3::GoBMoretoMiss0(uint64_t ubf) {
	if (!ubf) return ;
	for (uint64_t i = 0, bit = 1; i < xq.nout; i++, bit <<= 1) {
		register uint32_t u = xq.tout[i];
		if (bit & ubf) {// new crit
			xq.t2b[xq.n2b++] = u;
			xq.critbf |= u;
		}
		else xq.tin[xq.nin++] = u; // put it in to check later
	}
	xq.nmiss = xq.nout = 0;
	xq.SetFilters();
	register uint32_t F = xq.fa, A = xq.fb;
	if (xq.nin) {// check xq.in potential 
		while (1) {// open the door tomore than one assign
			register uint32_t Fr = F, nn = xq.nin;
			xq.nin = 0;
			for (uint32_t i = 0; i < nn; i++) {
				register uint32_t U = xq.tin[i];
				MISS0ADD;
			}
			if (Fr == F) break;;
		}
	}
	if (_popcnt32(F) == xq.nb3) { GoC0F(F); return; }
	GoC0(F, A);
}
void STD_B3::GoBMoretoMiss1(uint64_t ubf) {
	if (g17b.VerifyValidb3())return;
	if (!ubf) return;
	for (uint64_t i = 0, bit = 1; i < xq.nout; i++, bit <<= 1) {
		register uint32_t u = xq.tout[i];
		if (bit & ubf) {// new crit
			xq.t2b[xq.n2b++] = u;
			xq.critbf |= u;
		}
		else xq.tin[xq.nin++] = u; // put it in to check later
	}
	xq.nmiss = 1;
	xq.nout = 0;
	g17b.nt3more = 0;
	if (g17b.IsValidB3(xq.critbf)) {// not valid, new outfield
		register uint32_t U = g17b.anduab3;
		if (!U) return;
		GoB1toMiss0(U);
		return;
	}
	// now miss1 no out try all in
	XQ xqr = xq;
	g17b.TryMiss1Subcritical();
	xq = xqr;
	uint32_t U = BIT_SET_27 ^ xq.critbf;// dummy UA for any outfield
	GoB1toMiss0(U);
	return;

}


//____________processing band 3 to the end

int G17B::IsValid_myb12() {
	if (zh2b[1].IsValid(myb12)) {
		anduab12 = ~0;
		register uint64_t ua54;
		for (uint32_t i = 0; i < zh2gxn.nua; i++) {
			register uint64_t ua = zh2gxn.tua[i], cc = _popcnt64(ua);
			ua54 = (ua & BIT_SET_27) | ((ua & BIT_SET_B2) >> 5);
			anduab12 &= ua54;
			if (cc < 12) {
				cout << Char54out(ua54) << " seen add b12 size " << cc << endl;
				aigstop = 1; cout << " stop uab12<12" << endl; return 1;
			}
			if(op.f4)cout << Char54out(ua54) << " fresh b12 ntumore "<< ntumore << " [4] " << p_cpt2g[4] << endl;
			if (ntumore < MAXMORE)tumore[ntumore++]= ua54;
			if (cc < 22) {
				t54b12.AddA(ua54);	t54b12.AddB(ua54);	t54b12.AddC(ua54);
			}
		}
		ua_ret7p = ua54;// return last (smaller)
		return 1;
	}
	return 0;
}
uint32_t G17B::IsValidB3(uint32_t bf,int debug) {
	p_cpt2g[31]++;
	//cout << Char27out(bf) << "check b3 [31]"<< p_cpt2g[31] << endl;
	if (nt3more) {
		for (uint32_t i = 0; i < nt3more; i++)if (bf == t3more[i]) return t3more[i];
	}
	int nret;
	if ((nret=zhou[0].CallCheckB3( bf,(debug>1)))) {
		anduab3 = BIT_SET_27;
		for (int iadd = 0; iadd < nret; iadd++) {
			BF128 w = zhgxn.tua[iadd];
			int cc = _popcnt32(w.bf.u32[2]);
			if (!cc) {
				cout << Char54out(myb12) << " ";
				cout << Char27out(bf) << " bug no b3 IsValidB3 [7]"
					<< " [0]" << p_cpt2g[0] << " [3]" << p_cpt2g[3]
					<< " [4]" << p_cpt2g[4] << " [7]" << p_cpt2g[7]
					<< endl;
				aigstop = 1;	return 1;
			}
			register uint32_t ua = w.bf.u32[2];
			t3more[nt3more++] = ua;
			anduab3 &= ua;
			if (ua & ~t3infield)  t3outseen &= ua;

			register uint64_t U = w.bf.u64[0];
			uint64_t cc0 = _popcnt64(U);
			if (cc0 > 16)continue;
			if (!cc0) {
				cout << Char27out(bf) << " bug ua nob12 [8]"  << endl;
				aigstop = 1;	return 1;
			}

			U = (U & BIT_SET_27) | ((U & BIT_SET_B2) >> 5);// mode 54
			if (cc <= 6 && cc > 1) {
				if (cc > 3) {// is it a 2 digits??
					int ndigs = 0;
					for (int i = 0; i < 9; i++)
						if (ua & myband3->dpat[i]) ndigs++;
					if (ndigs == 2) {
						int i81 = myband3->GetI81_x(ua);
						if (i81 >= 0) {
							if (op.dv3) {
								int iz = guah54n.indg2[i81];
								int n = guah54n.zz[iz].n;
							}
							guah54n.AddA2(U, i81,(int)cc0);
							guah54n.g2.setBit(i81);
							p_cpt2g[20]++;
							continue;
						}
					}
					p_cpt2g[19]++;
					if (cc == 4) 	myband3->Addm4(w);
					else 	myband3->Addmm(w);
					continue;
				}

				else {
					if (cc == 2) {
						int i81 = myband3->GetI81_2(w.bf.u32[2]);
						guah54n.AddA2(U, i81,(int)cc0);
						guah54n.g2.setBit(i81);
						p_cpt2g[20]++;
					}
					else  {
						int i81 = myband3->GetI81_3(w.bf.u32[2]);						
						guah54n.AddA3(U, i81);
						guah54n.g3.setBit(i81);
						p_cpt2g[21]++;
					}
				}
			}
		}
		return 1;
	}
	else return 0;
}
int G17B::Valid3_1_3(uint32_t bf) {
	nt3more = 0;
	if (!IsValidB3(bf))return 0;
	for (uint32_t i = 0; i < nt3more; i++) {
		xq.tout[xq.nout++] = t3more[i];
	}
	nt3more = 0;
	return 1;
}
int  G17B::Valid3mm(uint32_t bf) {
	nt3more = 0;
	if (!IsValidB3(bf))return 0;
	for (uint32_t i = 0; i < nt3more; i++) {
		t3b[nt3b++] = t3more[i];
		xq.tout[xq.nout++] = t3more[i];
	}
	nt3more = 0;
	return 1;
}


//__________ new potential valid bands 1+2

int XQ::Min1_4Disjoint() {
	if (nout < 4)return 0;
	register uint32_t r1 = tout[0]|tout[1], r2=tout[0] & tout[1],r3,r4,x;
	x = tout[2]; r3 = r2 & x; r2 |= r1 & x; r1 |= x;
	x = tout[3]; r4 = r3 & x; r3 |= r2 & x; r2 |= r1 & x; r1 |= x;
	for (uint32_t i = 4; i < nout; i++) {
		x = tout[i];
		r4 |= r3 & x; r3 |= r2 & x; r2 |= r1 & x; r1 |= x;
	}
	if (r4)return 3; else if (r3) return 2; else if (r2) return 1; else return 0;
}
int XQ::Miss1ToMiss0(int debug) {
	if (!nout) {
		cout << "bug miss1 to miss0" << endl;
		g17b.aigstop = 1;		return 1;	}
	{
		register uint32_t A; if (!(A = GetAndout())) return 1;
		t2b[n2b++] = A;
		critbf |= A;
		nout = nmiss = 0;
		SetFilters();
	}
	if (!nin) return 0;
	while (1) {// open the door tomore than one assign
		int as = 0;
		{
			register uint32_t F = fa, A = fb;
			uint32_t n = nin;
			nin = 0;
			for (uint32_t i = 0; i < n; i++) {
				register uint32_t U = tin[i];
				if (F & U) continue;
				if (!(U &= A)) return 1;
				tin[nin++] = U;
				if (_popcnt32(U) == 1) as = U;
			}			
		}
		if (!as) return 0;
		AddAssigned(as);
	}
}
int XQ::MissxToMiss0(uint32_t ubf) {
	if (!ubf) return 0;
	for (uint32_t i = 0, bit = 1; i < nout; i++, bit <<= 1) {
		register uint32_t u = tout[i];
		if (bit & ubf) {// new crit
			t2b[n2b++] = u;
			critbf |= u;
		}
		else tin[nin++] = u; // put it in to check later
	}

	nout = nmiss = 0;
	SetFilters();
	if (!nin) return 0;
	while (1) {// open the door tomore than one assign
		int as = 0;
		{
			register uint32_t F = fa, A = fb;
			uint32_t n = nin;
			nin = 0;
			for (uint32_t i = 0; i < n; i++) {
				register uint32_t U = tin[i];
				if (F & U) continue;
				if (!(U &= A)) return 1;
				tin[nin++] = U;
				if (_popcnt32(U) == 1) as = U;
			}
		}
		if (!as) return 0;
		AddAssigned(as);
	}
}
int XQ::Miss0CheckTin() {// see if new invalid or new assigned 
	if (nmiss || (!nin)) return 0;
	// check here if fresh potential in "in table"
	while (1) {// open the door tomore than one assign
		int as = 0;
		{
			register uint32_t F = fa, A = fb;
			int n = 0;
			for (uint32_t i = 0; i < nin; i++) {
				register uint32_t U = tin[i];
				if (F & U) continue;
				if (!(U &= A)) return 1;
				tin[n++] = U;
				if (_popcnt32(U) == 1) as = U;
			}
			nin = n;
		}
		if (!as) return 0;
		AddAssigned(as);
	}
}
uint64_t XQ::Isoutsize2() {
	if (nout < 2) return 0;
	register uint32_t n = nout;
	if (n > 64) n = 64;
	for (uint32_t i1 = 0; i1 < n - 1; i1++) {
		register uint32_t U1 = tout[i1];
		for (uint32_t i2 = i1+1; i2 < n; i2++) {
			register uint32_t U2 = tout[i2];
			if (U1 & U2) continue;
			return ((uint64_t)1 << i1) | ((uint64_t)1 << i2);
		}
	}
	return 0;
}
uint64_t XQ::Isoutsize3() {
	if (nout < 3) return 0;
	register uint32_t n = nout;
	if (n > 64) n = 64;
	for (uint32_t i1 = 0; i1 < n - 2; i1++) {
		register uint32_t U1 = tout[i1];
		for (uint32_t i2 = i1 + 1; i2 < n-1; i2++) {
			register uint32_t U2 = tout[i2];
			if (U1 & U2) continue;
			for (uint32_t i3 = i2 + 1; i3 < n; i3++) {
				register uint32_t U3 = tout[i3];
				if ((U1 | U2) & U3) continue;
				return ((uint64_t)1 << i1) | ((uint64_t)1 << i2) | ((uint64_t)1 << i3);
			}
		}
	}
	return 0;
}
uint64_t XQ::Isoutsize4() {
	if (nout < 4) return 0;
	register uint32_t n = nout;  
	if (n > 64) n = 64;
	for (uint32_t i1 = 0; i1 < n-3; i1++) {
		register uint32_t U1 = tout[i1];
		for (uint32_t i2 = i1 + 1; i2 < n-2; i2++) {
			register uint32_t U2 = tout[i2];
			if (U1 & U2) continue;
			for (uint32_t i3 = i2 + 1; i3 < n-1; i3++) {
				register uint32_t U3 = tout[i3];
				if ((U1 | U2) & U3) continue;
				register uint32_t uo3 = U1 | U2 |U3;
				for (uint32_t i4 = i3 + 1; i4 < n ; i4++) {
					register uint32_t U4 = tout[i4];
					if (uo3 & U4) continue;
					return ((uint64_t)1 << i1) | ((uint64_t)1 << i2) |
						((uint64_t)1 << i3) | ((uint64_t)1 << i4);
				}
			}
		}
	}
	return 0;
}
void XQ::CleanIn() {// usually miss1 last step
	uint32_t nn = nin; nin = 0;
	uint32_t tx[7][100],ntx[7];
	memset(ntx, 0, sizeof ntx);
	for (uint32_t i = 0; i < nn; i++) {
		register uint32_t u = tin[i],nu=~u;
		for (uint32_t j = 0; j < n2a; j++) {
			if (!(t2a[j] & nu)) { u = 0; break; }
		}
		if (!u) continue;
		for (uint32_t j = 0; j < n2b; j++) {
			if (!(t2b[j] & nu)) { u = 0; break; }
			// see also reverse ?? reducing t2b
		}
		if (u) {
			register uint32_t cc = _popcnt32(u);
			if (cc > 6)cc = 6;
			tx[cc][ntx[cc]++] = u;
		}
	}
	nin = 0;
	for (uint32_t i = 0; i < 7; i++) if (ntx[i]) {
		register uint32_t* tu = tx[i];
		for (uint32_t j = 0; j < ntx[i]; j++) {
			register uint32_t U = tu[j], nU = ~U;
			for (uint32_t k = 0; k < nin; k++) {
				if (!(tin[k] & nU)) { U = 0; break; }
			}
			if (U)tin[nin++] = U;
		}
	}
}
void XQ::CleanOut() {// usually miss1 last step
	uint32_t nn = nout; nout = 0;
	uint32_t tx[8][100], ntx[7];
	memset(ntx, 0, sizeof ntx);
	for (uint32_t i = 0; i < nn; i++) {
		register uint32_t u = tout[i],  cc = _popcnt32(u);
		if (cc > 6)cc = 6;
		tx[cc][ntx[cc]++] = u;		
	}
	for (uint32_t i = 0; i < 7; i++) if (ntx[i]) {
		register uint32_t* tu = tx[i];
		for (uint32_t j = 0; j < ntx[i]; j++) {
			register uint32_t U = tu[j], nU = ~U;
			for (uint32_t k = 0; k < nout; k++) {
				if (!(tout[k] & nU)) { U = 0; break; }
			}
			if (U)tout[nout++] = U;
		}
	}
}
void XQ::CleanOut(uint32_t F, uint32_t A) {// usually miss1 last step
	uint32_t nn = nout; nout = 0;
	uint32_t tx[7][100], ntx[7];
	memset(ntx, 0, sizeof ntx);
	for (uint32_t i = 0; i < nn; i++) {
		register uint32_t u = tout[i];
		if (u & F) continue;
		u &= A;
		register uint32_t cc = _popcnt32(u);
		if (cc > 6)cc = 6;
		tx[cc][ntx[cc]++] = u;
	}
	for (uint32_t i = 0; i < 7; i++) if (ntx[i]) {
		register uint32_t* tu = tx[i];
		for (uint32_t j = 0; j < ntx[i]; j++) {
			register uint32_t U = tu[j], nU = ~U;
			for (uint32_t k = 0; k < nout; k++) {
				if (!(tout[k] & nU)) { U = 0; break; }
			}
			if (U)tout[nout++] = U;
		}
	}
}


void  G17B::GoEndAll(uint32_t bf, uint32_t ac, int debug) {//  call the relevant expand b3
	ac &= BIT_SET_27;// be sure to have no extra digit
	int ass = _popcnt32(bf);
	ntoassb3 = xq.nb3-ass;
	if (debug) {
		cout << "entry go endall ntoassb3 = " << ntoassb3
			<< " clean_valid_done " << clean_valid_done << endl;
		cout << Char54out(myb12) << " myb12" << endl;

	}
	if (VerifyValidb3())return;
	if (debug) {
		cout << "valid b12 " << endl;
		if (bf) cout << Char27out(bf )<< " bf entry" << endl;
		xq.DumpOut();
	}

	if (ntoassb3 == 1) {
		int x,u;
		if (!xq.nout) {
			if (!IsValidB3(bf))u = ac;
			else u= anduab3;
		}
		else // must try a possible "17"belox"
			if (!(u = xq.GetAndout())) return; // no single clue
		while (bitscanforward(x, u)) {
			register int bit= 1 << x;
			u ^= bit;
			if (IsValidB3(bf | bit)) u &= anduab3;
			else Out17(bf | bit);
		}
		return;
	}
	if (ntoassb3 >= 4) {
		GoB3Expand_1_3(bf,ac,debug);
		return;
	}
	if (debug)cout << "BuildSortT3b(); " << endl;
	BuildSortT3b();
	SP3 sp3;
	sp3.active = ac;
	sp3.all_previous = bf;
	GoB3Expand_4_x(sp3);
}

//________________________________________________________

void G17B::BuildSortT3b() {
	uint32_t tx[7][100], ntx[7];
	memset(ntx, 0, sizeof ntx);
	for (uint32_t i = 0; i < xq.nout; i++) {
		register uint32_t U = xq.tout[i] , cc = _popcnt32(U);
		if (cc > 6)cc = 6;
		tx[cc][ntx[cc]++] = U;
	}
	nt3b = 0;
	for (uint32_t i = 0; i < 7; i++) if (ntx[i]) {
		register uint32_t* tu = tx[i];
		for (uint32_t j = 0; j < ntx[i]; j++) {
			register uint32_t U = tu[j], nU = ~U;
			for (uint32_t k = 0; k < nt3b; k++) {
				if (!(t3b[k] & nU)) { U = 0; break; }
			}
			if (U)t3b[nt3b++] = U;
		}
	}
}
int G17B::SortT3o(uint32_t active) {// order t3o on size
	if (!active) {
		uint32_t t4[200], t6[100], tm[100], nt4 = 0, nt6 = 0, ntm = 0;
		for (uint32_t i = 0; i < nt3o; i++) {
			register uint32_t U = t3o[i], cc = _popcnt32(U);
			if (cc < 5)t4[nt4++] = U;
			else if (cc < 7)t6[nt6++] = U;
			else tm[ntm++] = U;
		}
		int n = 0;
		for (uint32_t i = 0; i < nt4; i++)t3o[n++] = t4[i];
		for (uint32_t i = 0; i < nt6; i++)t3o[n++] = t6[i];
		for (uint32_t i = 0; i < ntm; i++)t3o[n++] = tm[i];
		return n;
	}
	// apply active and sort 
	uint32_t tx[7][100], ntx[7];
	memset(ntx, 0, sizeof ntx);
	register uint32_t A = active;
	for (uint32_t i = 0; i < nt3o; i++) {
		register uint32_t U = t3o[i]&A, cc = _popcnt32(U);
		if (cc >6)cc=6;
		uint32_t* t = tx[cc], n = ntx[cc];
		for (uint32_t j = 0; j < n; j++) {// clear =
			if (t[j] ==U) { U = 0; break; }
		}
		if(U)tx[cc][ntx[cc]++] = U;
	}
	nt3o = 0;
	if (ntx[0]) return 1;
	for (uint32_t i = 1; i < 7; i++) if (ntx[i]) {
		register uint32_t *tu = tx[i];
		for (uint32_t j = 0; j < ntx[i]; j++) {
			register uint32_t U = tu[j],nU=~U;
			for (uint32_t k = 0; k < nt3o; k++) {
				if (!(t3o[k] & nU)) { U = 0; break; }
			}
			if (U)t3o[nt3o++] = U;
		}
	}
	return 0;
}

void G17B::GoB3Expand_1_3(uint32_t bf, uint32_t ac, int debug ) {
	SP3 spb[5];
	spb[0].all_previous = bf;	
	spb[0].active = ac&BIT_SET_27;	
	spb[0].indtw3 = 0;// initial first ua
	spb[0].possible_cells = xq.tout[0];
next1:
	{// catch and apply cell in bitfields
		register int cell;
		register uint32_t p = spb[0].possible_cells;
		if (!p) return;		
		bitscanforward(cell, p);
		register uint32_t bit = 1 << cell;
		spb[0].possible_cells ^= bit;
		spb[0].active ^= bit;
		spb[1] = spb[0];
		spb[1].all_previous |= bit;
		register uint32_t F = spb[1].all_previous;
		for (uint32_t i = spb[0].indtw3 + 1; i < xq.nout; i++) {
			register uint32_t U = xq.tout[i];
			if (!(U & F)) {
				U &= spb[1].active;
				spb[1].possible_cells = U;
				spb[1].indtw3 = i;
				goto next2;
			}
		}
		if (VerifyValidb3()) return;
		if (Valid3_1_3(spb[1].all_previous))goto next1;
		spb[1].possible_cells = 0; // see later 
	}
next2:
	{// catch and apply cell in bitfields
		register int cell;
		register uint32_t p = spb[1].possible_cells;
		if (!p) goto next1;
		bitscanforward(cell, p);
		register uint32_t bit = 1 << cell;
		spb[1].possible_cells ^= bit;
		spb[1].active ^= bit;
		spb[2] = spb[1];
		spb[2].all_previous |= bit;
		register uint32_t F = spb[2].all_previous;
		for (uint32_t i = spb[1].indtw3 + 1; i <xq.nout; i++) {
			register uint32_t U = xq.tout[i];
			if (!(U & F)) {
				U &= spb[2].active;
				if (!U)goto next2;// dead branch 
				spb[2].possible_cells = U;
				spb[2].indtw3 = i;
				goto next3;
			}
		}
		if (VerifyValidb3()) return;
		if (Valid3_1_3(spb[2].all_previous))goto next2;
		spb[2].possible_cells = 0; // see later 
	}
next3:
	{// catch and apply cell in bitfields
		register int cell;
		register uint32_t p = spb[2].possible_cells;
		if (!p) goto next2;
		bitscanforward(cell, p);
		register uint32_t bit = 1 << cell;
		spb[2].possible_cells ^= bit;
		spb[2].active ^= bit;
		spb[3] = spb[2];
		spb[3].all_previous |= bit;
	}
	if (ntoassb3 != 4) goto endnext3;
	// this is the last step for 4
	{
		register uint32_t F = spb[3].all_previous,
			wa = spb[2].active, n = 0;
		for (uint32_t i = spb[2].indtw3 + 1; i < xq.nout; i++) {
			register uint32_t U = xq.tout[i];
			if (!(U & F)) {
				n++;
				if (!(wa &= U)) goto next3; // dead
			}
		}
		if (VerifyValidb3()) return;// not sure it is done
		if (!n) {// could be a valid
			if (Valid3_1_3(spb[3].all_previous))
			wa = anduab3;
		}
		uint32_t cell;
		while (bitscanforward(cell, wa)) {
			register uint32_t bit = 1 << cell,
				bf= spb[3].all_previous | bit;
			wa ^= bit; //clear bit
			if (Valid3_1_3(bf))
				wa &= anduab3;
			else 	Out17(bf);//can be valid 17 in 18 mode
		}
	}
	goto next3;
endnext3:
	{// build a reduced table for the next clues
		nt3b = 0;
		uint32_t tx[8][50], ntx[7];// gives 60 for 6 and more 
		memset(ntx, 0, sizeof ntx);
		register uint32_t A = spb[2].active, F = spb[3].all_previous;
		for (uint32_t i = spb[2].indtw3 + 1; i < xq.nout; i++) {
			register uint32_t U =xq.tout[i];
			if (U & F) continue;
			if (!(U &= A)) goto next3;
			register uint32_t cc = _popcnt32(U);
			if (cc > 6)cc = 6;
			tx[cc][ntx[cc]++] = U;
		}
		for (uint32_t i = 1; i < 7; i++) if (ntx[i]) {
			register uint32_t* tu = tx[i];
			for (uint32_t j = 0; j < ntx[i]; j++) {
				register uint32_t U = tu[j], nU = ~U;
				for (uint32_t k = 0; k < nt3b; k++) {
					if (!(t3b[k] & nU)) { U = 0; break; }
				}
				if (U)t3b[nt3b++] = U;
			}
		}
		if (!nt3b) {// still un assigned >=2 can not be valid
			if (VerifyValidb3()) return;
			if (!Valid3_1_3(spb[3].all_previous))goto next3;
			for (uint32_t i = 0; i < zhgxn.nua; i++) {
				BF128 ww = zhgxn.tua[i];
				t3b[nt3b++] = ww.bf.u32[2];
			}
		}
		GoB3Expand_4_x(spb[3]);
		if (clean_valid_done == 2) return;
		goto next3;
	}
	goto next3;// not expected
}
void G17B::GoB3Expand_4_x(SP3 spe, int debug ) {
	int ntoass = ncluesb3 - _popcnt32(spe.all_previous);
	uint64_t limspot = ntoass - 1, limm1 = limspot - 1;
	SP3 spb[12];
	register SP3* s, * sn;
	register uint64_t ispot;
	s = spb;
	spb[0] = spe;
	s->indtw3 = 0;// initial first ua
	s->possible_cells = t3b[0];
next:
	ispot = s - spb;
	{// catch and apply cell in bitfields
		register int cell;
		register uint32_t p = s->possible_cells;
		if (!p)if (--s >= spb)goto next; else return;
		bitscanforward(cell, p);
		register uint32_t bit = 1 << cell;
		s->possible_cells ^= bit;
		s->active ^= bit;
		sn = s + 1; *sn = *s;
		sn->all_previous |= bit;
	}
	if (ispot < limm1) { 
		register uint32_t F = sn->all_previous;
		for (uint32_t i = s->indtw3 + 1; i < nt3b; i++) {
			register uint32_t U = t3b[i];
			if (!(U & F)) {
				U &= s->active;
				if (!U)goto next;//dead branch
				sn->possible_cells = U;
				sn->indtw3 = i;
				s++; // switch to next spot
				goto next;
			}
		}

		// no ua available must check( in 18 mode can  be valid)
		if (VerifyValidb3())  return; 
		if (IsValidB3(sn->all_previous)) {
			sn->possible_cells = anduab3&sn->active;
			sn->indtw3 = nt3b;// no more ua later
			s++;	goto next;// switch to next spot
		}
		else 	Out17(sn->all_previous);//can be valid 17 in 18 mode
	}

	// this is the last step must hit all pending uas
	{ // find next cells hitting all uas
		int aig = 1;
		register uint32_t andw = sn->active ;
		register uint32_t F = sn->all_previous;
		{// and still valid   uas
			for (uint32_t i = s->indtw3 + 1; i < nt3b; i++) {
				register uint32_t U = t3b[i];
				if (!(U & F)) { // not hit ua
					if (!(andw &= U))goto next;//dead branch
					aig = 0;
				}
			}
		}
		// no more ua or "and all uas" not empty
		if (VerifyValidb3())  return;
		if (aig) {// no ua could be a 17 valid in 18 mode 
			if (Valid3mm(F)) 	andw &= anduab3;			 
			else { Out17(F);	goto next; }// this is a valid 17
		}
		if (!andw)goto next;  
		register int cell;
		while (bitscanforward(cell, andw)) {
			register uint32_t bit = 1 << cell;
			andw ^= bit; //clear bit
			if (Valid3mm(F | bit)) 	andw &= anduab3;			
			else 	Out17(F | bit);			
		}
		goto next;
	}
	goto next;// never here
}




//=========brute force specific to this
int ZHOU::CallCheckB3( uint32_t bf, int nogo) {// 17 search mode
	zh_g.diag = nogo;
	memcpy(this, zhoustart, sizeof zhoustart);
	misc.SetAll_0();
	BF128 dca[9];
	memset(dca, 0, sizeof dca);
	int digitsbf = 0;

	{// cells in bands 1+2		
		int cell;
		register uint64_t U = g17b.myb12;
		while (bitscanforward64(cell, U)) {
			U ^= (uint64_t)1 << cell;
			int  digit = g17b.grid0[cell];
			int xcell = C_To128[cell]; // the cell value in 3x32 of a 128 bits map
			digitsbf |= 1 << digit;
			Assign(digit, cell, xcell);
			dca[digit].Set(xcell);
		}
	}

	{
		uint32_t cc;
		register int x = bf;
		while (bitscanforward(cc, x)) {
			x ^= 1 << cc; //clear bit
			int cell = cc + 54, digit = g17b.grid0[cell];
			digitsbf |= 1 << digit;
			int xcell = cc + 64; // the cell value in 3x32 of a 128 bits map
			Assign(digit, cell, xcell);
			dca[digit].Set(xcell);
		}
	}
	zh_g2.s17_b3_mini = 1;
	BF128 w = cells_unsolved;
	w.bf.u32[3] = ~0;// keep rowunsolved settled
	for (int i = 0; i < 9; i++)  FD[i][0] &= w | dca[i];
	//__________end assign last lot start solver
	zhgxn.nua = 0;
	zh_g.go_back = 0;	zh_g.nsol = 0; zh_g.lim = 1;// modevalid is set to  1
	int ir = Full17Update();
	if (ir == 2) return 0;// solved can not be multiple
	Guess17(0);
	return zhgxn.nua;
}

int ZHOU::PartialInitSearch17(uint32_t* t, int n) {
	zh_g2.digitsbf = 0;
	memset(zh_g2.Digit_cell_Assigned, 0, sizeof zh_g2.Digit_cell_Assigned);
	memcpy(this, zhoustart, sizeof zhoustart);
	for (int icell = 0; icell < n; icell++) {
		int cell = t[icell], digit = g17b.grid0[cell];
		int xcell = C_To128[cell]; // the cell value in 3x32 of a 128 bits map
		zh_g2.digitsbf |= 1 << digit;
		if (FD[digit][0].Off(xcell))  return 1;// check not valid entry
		Assign(digit, cell, xcell);
		zh_g2.Digit_cell_Assigned[digit].Set(xcell);
	}
	//cout << "ok init" << endl;
	BF128 w = cells_unsolved;
	w.bf.u32[3] = ~0;// keep rowunsolved settled
	for (int i = 0; i < 9; i++)  FD[i][0] &= w | zh_g2.Digit_cell_Assigned[i];
	return 0;
}

int ZHOU::Apply17SingleOrEmptyCellsB12() {
	zh_g.single_applied = 0;
	// here  singles and empty cells till 4 cells searched
	register uint64_t R1, R2, R3, R4;
	{
		register uint64_t* P = FD[0][0].bf.u64, M = *P;
		R1 = M;
		P += 4; M = *P;	                            R2 = R1 & M;  R1 |= M;
		P += 4; M = *P;              R3 = R2 & M;   R2 |= R1 & M; R1 |= M;
		P += 4; M = *P; R4 = R3 & M;  R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 4; M = *P;	R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 4; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 4; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 4; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 4; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
	}
	if (cells_unsolved.bf.u64[0] & (~R1)) 	return 1; // empty cells
	R1 &= ~R2; // now true singles
	R1 &= cells_unsolved.bf.u64[0]; // these are new singles
	if (R1) {// singles to apply
		uint32_t xcell;
		while (bitscanforward64(xcell, R1)) {
			R1 ^= (uint64_t)1 << xcell;
			uint32_t cell = From_128_To_81[xcell];
			for (int idig = 0; idig < 9; idig++) {
				if (FD[idig][0].On(xcell)) {
					Assign(idig, cell, xcell);
					goto nextr1;
				}
			}
			return 1; // conflict with previous assign within this lot
		nextr1:;
		}
		zh_g.single_applied = 1;
		return 0;
	}
	// no single store apply  pair in priority ??
	R2 &= ~R3; // now true singles
	if (!R2) {
		R3 &= ~R4;
		if (R3) R2 = R3;
		else R2 = R4;
	}
	bitscanforward64(zh_g2.xcell_to_guess, R2);
	return 0;
}
int ZHOU::Apply17SingleOrEmptyCellsB3() {
	zh_g.single_applied = 0;
	// here  singles and empty cells till 4 cells searched
	register uint32_t R1, R2, R3, R4;
	{
		register uint32_t* P = &FD[0][0].bf.u32[2], M = *P;
		R1 = M;
		P += 8; M = *P;	                            R2 = R1 & M;  R1 |= M;
		P += 8; M = *P;              R3 = R2 & M;   R2 |= R1 & M; R1 |= M;
		P += 8; M = *P; R4 = R3 & M;  R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 8; M = *P;	R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 8; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 8; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 8; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
		P += 8; M = *P; R4 |= R3 & M; R3 |= R2 & M; R2 |= R1 & M; R1 |= M;
	}
	if (cells_unsolved.bf.u32[2] & (~R1)) 	return 1; // empty cells
	R1 &= ~R2; // now true singles
	R1 &= cells_unsolved.bf.u32[2]; // these are new singles
	if (R1) {// singles to apply in band 3
		uint32_t xcell;
		while (bitscanforward(xcell, R1)) {
			R1 ^= (uint64_t)1 << xcell;
			uint32_t cell = xcell + 54;
			xcell += 64;
			for (int idig = 0; idig < 9; idig++) {
				if (FD[idig][0].On(xcell)) {
					Assign(idig, cell, xcell);
					goto nextr1;
				}
			}
			return 1; // conflict with previous assign within this lot
		nextr1:;
		}
		zh_g.single_applied = 1;
		return 0;
	}
	// no single store apply  pair in priority ??
	R2 &= ~R3; // now true pairs
	if (!R2) {
		R3 &= ~R4; // now true tripletss
		if (R3) R2 = R3;
		else R2 = R4;
	}
	bitscanforward(zh_g2.xcell_to_guess, R2);
	zh_g2.xcell_to_guess += 64;
	return 0;
}
int ZHOU::Full17Update() {
	if (zh_g.go_back) return 0;
	while (1) {
		if (!Update()) return 0; // game locked in update
		//if(diag &&cells_unsolved.bf.u32[2]==0)ImageCandidats();
		if (!Unsolved_Count()) return 2;
		if (cells_unsolved.bf.u32[2]) {// fill B3 first
			if (Apply17SingleOrEmptyCellsB3())	return 0; //  empty cell or conflict singles in cells
		}
		else {
			if ((!ISFALSEON))return 0;
			if (Apply17SingleOrEmptyCellsB12())	return 0;
		}
		if (!zh_g.single_applied)	break;
	}
	return 1;
}
void ZHOU::Compute17Next(int index) {
	int ir = Full17Update();
	if (zh_g.diag) {
		cout << "index=" << index << endl;
		ImageCandidats();
	}
	if (!ir) return;// locked 
	if (ir == 2) {//solved
		if (index) {// store false as ua
			BF128  wua;
			int* sol = g17b.grid0;
			wua.SetAll_0();
			for (int i = 0; i < 81; i++) {
				int d = sol[i];
				if (FD[d][0].Off_c(i))	wua.Set_c(i);
			}
			if (wua.isNotEmpty()) {
				//if (zh_g.diag) {
					//cout << "zhgxn.nua=" << zhgxn.nua << endl;
					//wua.Print3(" ");
				//}
				int cc = _popcnt32(wua.bf.u32[2]);
				if ((!zhgxn.nua) || cc < 3)
					zhgxn.tua[zhgxn.nua++] = wua;
				if (cc < 3 || zhgxn.nua>5)	zh_g.go_back = 1;
			}
		}
		return;
	}
	Guess17(index);// continue the process
}
void ZHOU::Guess17(int index) {
	if (zh_g.go_back) return;
	int xcell = zh_g2.xcell_to_guess,
		cell = From_128_To_81[xcell],
		digit = g17b.grid0[cell];
	// true first if possible
	if (FD[digit][0].On(xcell)) {
		ZHOU* mynext = (this + 1);
		*mynext = *this;
		mynext->SetaCom(digit, cell, xcell);
		mynext->Compute17Next(index + 1);
		if (zh_g.go_back) return;
	}
	for (int idig = 0; idig < 9; idig++) {
		if (idig == digit)continue;
		if (ISFALSEON && zhgxn.nua) continue;
		if (FD[idig][0].On(xcell)) {
			ZHOU* mynext = (this + 1);
			*mynext = *this;
			if (cell >= 54)mynext->ISFALSEON++;
			mynext->SetaCom(idig, cell, xcell);
			mynext->Compute17Next(index + 1);
			if (zh_g.go_back) return;
		}
	}
}

void G17B::Out17(uint32_t bfb3) {
	if ((_popcnt32(bfb3) + _popcnt64(myb12)) > 17) {
		cout << Char54out(myb12) << " ";
		cout <<Char27out(bfb3) << " more than 17 out17  "  
		<< " [0]"<< p_cpt2g[0] << " [3]" << p_cpt2g[3]
			<< " [4]" << p_cpt2g[4] << " [7]" << p_cpt2g[7]
			<< endl;
		aigstop = 1;		return;	}

	myband3->poutdone++;
	char ws[128];
	strcpy(ws, empty_puzzle);
	{// cells in bands 1+2		
		int cell;
		register uint64_t U = myb12;
		while (bitscanforward64(cell, U)) {
			U ^= (uint64_t)1 << cell;
			ws[cell] = grid0[cell] + '1';
		}
	}

	for (int i = 0, bit = 1; i < 27; i++, bit <<= 1)if (bfb3 & bit)
		ws[i+54]= grid0[i+54] + '1';
	sprintf(&ws[81], ";%3d;%3d;%3d;%5d", genb12.i1t16, genb12.i2t16, t416_to_n6[myband3->i416],(int)( genb12.nb12 >> 6));
	fout1 << ws << endl;
	
	a_17_found_here++;

}