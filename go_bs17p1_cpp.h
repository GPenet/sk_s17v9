
void G17B::Init17p1() {
	b1maxcl = b2maxcl = 6;
	b2maxcl11 = 6;
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
		ac_clt[6] = ac_clt[5];
		Ac_px_6clues(ac_clt[6], bf_clt[5]);
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
		if (op.f3 && (op.f3 == p_cpt2g[3])) {
			cout << Char54out(bf_clt[5]) << "  6  [4] " << p_cpt2g[4]
				<< "   [3] " << p_cpt2g[3] << endl;
			cout << Char54out(ac_clt[6])<<" active" << endl;
		}
		Expand7();		if (aigstop) return;
	}
}

void G17B::Expand7() {
	if (Debugk(6))return;
	if (aigstop) return;
	int locdiag = 0;
	if (op.f4 && (op.f4 < p_cpt2g[4])) { aigstop = 1; return; }
	if (op.f4 == p_cpt2g[4] || op.opcode==10) {
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
	ua_t[6] = twu[0];
	if (locdiag) {
		cout << Char54out(ua_t[6]) << " ua for 7" << endl;
		cout << Char54out(ac_clt[6]) << "active ac_clt[6] start " << endl;
	}
	while (bitscanforward64(cl_t[6], ua_t[6])) {
		{NEWCLUE(5, 6)}
		if (locdiag)cout << Char54out(bf_clt[6]) << " next 7 clues" << endl;
		p_cpt2g[52]	++;
		ac_clt[7] = ac_clt[6];
		Ac_px_7clues(ac_clt[7], bf_clt[6]);// apply filter 7 clues
		t54b12.AddVect7(cl_t[6], vc_t[0]);
		int nuout = bbb54.GetBuildC(ac_clt[7], vc_t[0], 30);
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
		int nsizea[5] = { 0,0,0,0,0 };
		uint64_t ac0 = ac_clt[6];
		{
			uint64_t na = _popcnt64(ac_clt[6]);
			if (locdiag) cout << na << " active " << " limit 32 to ook for" << endl;
			if (na <= 32) {//54-7clues-15dead to look for early backtracking
				//bbb54.DumpOut();
				bbb54.CutToSize(na/3);
				if (DisjointsSize3B(ac0, bbb54.uout, bbb54.nuout, nsizea, locdiag)) continue;
				if (locdiag) 	cout << Char54out(ac0) << "active end " << nsizea[1] << endl;
			}
		}
		p_cpt2g[53]	++;
		if (nsizea[1] && ac0!= ac_clt[6]) {
			if (locdiag)bbb54.DumpOut();
			Expand7crit(ac0); continue; }
		p_cpt2g[54]	++;
		ua_t[7] = bbb54.uout[0];
		Expand8();		if (aigstop) return;
	}
}
void G17B::Expand7crit(uint64_t ac0){
	p_cpt2g[55]	++;
	int locdiag = 0;
	if (op.f4 == p_cpt2g[4] && op.ton) {
		cout << Char54out(bf_clt[6]) << " 7 crit " << endl;
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
	else {
		cout << "ntu7=0 [4]" << p_cpt2g[4] << "  [56]" << p_cpt2g[56] << endl;
		bbb54.DumpOut();
	}

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
			Valid8(); continue;// we have a valid 8
		}
		int nsizea[5] = { 0,0,0,0,0 };
		uint64_t ac0 = ac_clt[7],na = _popcnt64(ac0);
		if (locdiag) 	cout << Char54out(ac0) << "active 8 na=" <<na<< endl;
		if (locdiag)bbb54.DumpOut();
		bbb54.CutToSize(12);
		if(0){
			if (locdiag) cout << na << " active " << " limit 32 to look for" << endl;
			if (na <= 32) {//54-7clues-15dead to look for early backtracking
				//bbb54.DumpOut();
				bbb54.CutToSize(na / 3);
				if (DisjointsSize3(ac0, bbb54.uout, bbb54.nuout, nsizea, locdiag)) continue;
				if (locdiag) 	cout << Char54out(ac0) << "active end " << nsizea[1] << endl;

			}
		}

		if (DisjointsSize2B(ac0, bbb54.uout, bbb54.nuout,	nsizea,locdiag)) continue;		
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
	if (op.f4 == p_cpt2g[4] || op.opcode==10 ) {
		cout << Char54out(bf_clt[7]) << " 8 clues entry expand 9" << endl;
		locdiag = 1;
	}
	while (bitscanforward64(cl_t[8], ua_t[8])) {
		{NEWCLUE(7, 8)}
		if (Debugk(9))continue;
		p_cpt2g[70]	++;
		ac_clt[9] = ac_clt[8];
		Ac_px_9clues(ac_clt[9], bf_clt[8]);
		t54b12.AddVect(cl_t[8], vc_t[1], vc_t[2]);
		{
			//register uint64_t U = bbb54.wand;
			register uint64_t U = bbb54.GetAndC(ac_clt[9],vc_t[2]);
			if (!U ) continue;
			if (!(~U)) {// potential valid 9
				if (op.f4)cout << Char54out(bf_clt[8]) << "no more uas potential 9 clues" << endl;
				ntu9 = 0;
				if (IsValid7pbf(bf_clt[8])) {	// fresh uas are in tu8
					U = anduab12 & ac_clt[8];
					if (locdiag) {
						cout << Char54out(U) << "not 9 clues new and" << endl;
						Table54Dump(tu9, ntu9);
					}
					if(!U )continue;
				}
				else {
					if (locdiag)cout << "valid 9 to do" << endl;
					Valid9();continue;
				}
			}
			ua_t[9] =U;
		}
		if (locdiag) {
			cout << Char54out(bf_clt[8]) << " 9 clues [70] "<< p_cpt2g[70] << endl;
			cout << Char54out(ac_clt[9]) << " active  for 10 " << endl;
			cout << Char54out(ua_t[9]) << " ua  for 10 " << endl;
		}
		p_cpt2g[71]	++;
		guah54n.Build9last();
		while (bitscanforward64(cl_t[9], ua_t[9])) {
			{NEWCLUE(8, 9)}
			if (locdiag) 		cout << Char54out(bf_clt[9]) << " 10 clues  " << endl;
			if (Debugk(10))continue;
			if (locdiag) {
				cout << Char54out(bf_clt[9]) << " 10 clues ok "  << endl;
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
				Valid9();	continue;
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
	if (Debugk(7))return;
	myb12 = bf_clt[6];
	guah54n.GetG2G3_7();// try 7
	CALLB3(7, 10);
	ac_clt[7] = ac_clt[6];
	Ac_px_7clues(ac_clt[7], bf_clt[6]);// apply filter 8 clues
	while (bitscanforward64(cl_t[7], ac_clt[7])) {// set clue 8
		uint64_t bit = (uint64_t)1 << cl_t[6];
		ac_clt[7] ^= bit; 	bf_clt[7] = bf_clt[6] | bit;
		Valid8();
	}
}
void G17B::Valid8() {
	if (Debugk(8))return;
	myb12 = bf_clt[7];
	guah54n.GetG2G3_8();// try 8
	CALLB3(8, 9);
	ac_clt[8] = ac_clt[7];
	Ac_px_8clues(ac_clt[8], bf_clt[7]);// apply filter 8 clues
	while (bitscanforward64(cl_t[8], ac_clt[8])) {// set clue 9
		uint64_t bit = (uint64_t)1 << cl_t[8];
		ac_clt[8] ^= bit; 		 bf_clt[8] = bf_clt[7] | bit;
		Valid9();
	}
}
void G17B::Valid9() {
	if (Debugk(9))return;
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
	ac_clt[9] = ac_clt[8];
	Ac_px_9clues(ac_clt[9], bf_clt[8]);// apply filter 9 clues
	if (op.p1)guah54n.Build9last();
	while (bitscanforward64(cl_t[9], ac_clt[9])) {// set clue 10
		uint64_t bit1 = (uint64_t)1 << cl_t[9];
		ac_clt[9] ^= bit1; 		bf_clt[9] = bf_clt[8] | bit1;		
		if (op.opcode == 10)		if (Debugk(10))continue;		
		Valid10();
	}
}
void G17B::Valid10() {
	if (Debugk(10))return;
	myb12 = bf_clt[9];
	if (op.p1) {
		guah54n.GetG2G3_10last();
		CALLB3(10, 7);		return;
	}
	guah54n.GetG2G3_10();
	CALLB3(10, 7);
	ac_clt[10] = ac_clt[9];
	if (Ac_px_10clues(ac_clt[10], bf_clt[9])) return;
	guah54n.Build10last();
	while (bitscanforward64(cl_t[10], ac_clt[10])) {
		register uint64_t bit2 = (uint64_t)1 << cl_t[10];
		ac_clt[10] ^= bit2; 
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


