#CD /D D:\Source\Repos\efop\EFOP_362\work\wp-a\a11\morse\dyngraph
#"c:\program files\python38\python" aes.py
  
#https://github.com/CryptoExperts/whibox_contest_submission_server/blob/whibox2019/aes.c
MAXKC = (256//32)
MAXKB = (256//8)
MAXNR = 14
"""
/*
Te0[x] = S [x].[02, 01, 01, 03];
Te1[x] = S [x].[03, 02, 01, 01];
Te2[x] = S [x].[01, 03, 02, 01];
Te3[x] = S [x].[01, 01, 03, 02];
Te4[x] = S [x].[01, 01, 01, 01];
Td0[x] = Si[x].[0e, 09, 0d, 0b];
Td1[x] = Si[x].[0b, 0e, 09, 0d];
Td2[x] = Si[x].[0d, 0b, 0e, 09];
Td3[x] = Si[x].[09, 0d, 0b, 0e];
Td4[x] = Si[x].[01, 01, 01, 01];
*/
"""
Te0 = [
    0xc66363a5, 0xf87c7c84, 0xee777799, 0xf67b7b8d,
    0xfff2f20d, 0xd66b6bbd, 0xde6f6fb1, 0x91c5c554,
    0x60303050, 0x02010103, 0xce6767a9, 0x562b2b7d,
    0xe7fefe19, 0xb5d7d762, 0x4dababe6, 0xec76769a,
    0x8fcaca45, 0x1f82829d, 0x89c9c940, 0xfa7d7d87,
    0xeffafa15, 0xb25959eb, 0x8e4747c9, 0xfbf0f00b,
    0x41adadec, 0xb3d4d467, 0x5fa2a2fd, 0x45afafea,
    0x239c9cbf, 0x53a4a4f7, 0xe4727296, 0x9bc0c05b,
    0x75b7b7c2, 0xe1fdfd1c, 0x3d9393ae, 0x4c26266a,
    0x6c36365a, 0x7e3f3f41, 0xf5f7f702, 0x83cccc4f,
    0x6834345c, 0x51a5a5f4, 0xd1e5e534, 0xf9f1f108,
    0xe2717193, 0xabd8d873, 0x62313153, 0x2a15153f,
    0x0804040c, 0x95c7c752, 0x46232365, 0x9dc3c35e,
    0x30181828, 0x379696a1, 0x0a05050f, 0x2f9a9ab5,
    0x0e070709, 0x24121236, 0x1b80809b, 0xdfe2e23d,
    0xcdebeb26, 0x4e272769, 0x7fb2b2cd, 0xea75759f,
    0x1209091b, 0x1d83839e, 0x582c2c74, 0x341a1a2e,
    0x361b1b2d, 0xdc6e6eb2, 0xb45a5aee, 0x5ba0a0fb,
    0xa45252f6, 0x763b3b4d, 0xb7d6d661, 0x7db3b3ce,
    0x5229297b, 0xdde3e33e, 0x5e2f2f71, 0x13848497,
    0xa65353f5, 0xb9d1d168, 0x00000000, 0xc1eded2c,
    0x40202060, 0xe3fcfc1f, 0x79b1b1c8, 0xb65b5bed,
    0xd46a6abe, 0x8dcbcb46, 0x67bebed9, 0x7239394b,
    0x944a4ade, 0x984c4cd4, 0xb05858e8, 0x85cfcf4a,
    0xbbd0d06b, 0xc5efef2a, 0x4faaaae5, 0xedfbfb16,
    0x864343c5, 0x9a4d4dd7, 0x66333355, 0x11858594,
    0x8a4545cf, 0xe9f9f910, 0x04020206, 0xfe7f7f81,
    0xa05050f0, 0x783c3c44, 0x259f9fba, 0x4ba8a8e3,
    0xa25151f3, 0x5da3a3fe, 0x804040c0, 0x058f8f8a,
    0x3f9292ad, 0x219d9dbc, 0x70383848, 0xf1f5f504,
    0x63bcbcdf, 0x77b6b6c1, 0xafdada75, 0x42212163,
    0x20101030, 0xe5ffff1a, 0xfdf3f30e, 0xbfd2d26d,
    0x81cdcd4c, 0x180c0c14, 0x26131335, 0xc3ecec2f,
    0xbe5f5fe1, 0x359797a2, 0x884444cc, 0x2e171739,
    0x93c4c457, 0x55a7a7f2, 0xfc7e7e82, 0x7a3d3d47,
    0xc86464ac, 0xba5d5de7, 0x3219192b, 0xe6737395,
    0xc06060a0, 0x19818198, 0x9e4f4fd1, 0xa3dcdc7f,
    0x44222266, 0x542a2a7e, 0x3b9090ab, 0x0b888883,
    0x8c4646ca, 0xc7eeee29, 0x6bb8b8d3, 0x2814143c,
    0xa7dede79, 0xbc5e5ee2, 0x160b0b1d, 0xaddbdb76,
    0xdbe0e03b, 0x64323256, 0x743a3a4e, 0x140a0a1e,
    0x924949db, 0x0c06060a, 0x4824246c, 0xb85c5ce4,
    0x9fc2c25d, 0xbdd3d36e, 0x43acacef, 0xc46262a6,
    0x399191a8, 0x319595a4, 0xd3e4e437, 0xf279798b,
    0xd5e7e732, 0x8bc8c843, 0x6e373759, 0xda6d6db7,
    0x018d8d8c, 0xb1d5d564, 0x9c4e4ed2, 0x49a9a9e0,
    0xd86c6cb4, 0xac5656fa, 0xf3f4f407, 0xcfeaea25,
    0xca6565af, 0xf47a7a8e, 0x47aeaee9, 0x10080818,
    0x6fbabad5, 0xf0787888, 0x4a25256f, 0x5c2e2e72,
    0x381c1c24, 0x57a6a6f1, 0x73b4b4c7, 0x97c6c651,
    0xcbe8e823, 0xa1dddd7c, 0xe874749c, 0x3e1f1f21,
    0x964b4bdd, 0x61bdbddc, 0x0d8b8b86, 0x0f8a8a85,
    0xe0707090, 0x7c3e3e42, 0x71b5b5c4, 0xcc6666aa,
    0x904848d8, 0x06030305, 0xf7f6f601, 0x1c0e0e12,
    0xc26161a3, 0x6a35355f, 0xae5757f9, 0x69b9b9d0,
    0x17868691, 0x99c1c158, 0x3a1d1d27, 0x279e9eb9,
    0xd9e1e138, 0xebf8f813, 0x2b9898b3, 0x22111133,
    0xd26969bb, 0xa9d9d970, 0x078e8e89, 0x339494a7,
    0x2d9b9bb6, 0x3c1e1e22, 0x15878792, 0xc9e9e920,
    0x87cece49, 0xaa5555ff, 0x50282878, 0xa5dfdf7a,
    0x038c8c8f, 0x59a1a1f8, 0x09898980, 0x1a0d0d17,
    0x65bfbfda, 0xd7e6e631, 0x844242c6, 0xd06868b8,
    0x824141c3, 0x299999b0, 0x5a2d2d77, 0x1e0f0f11,
    0x7bb0b0cb, 0xa85454fc, 0x6dbbbbd6, 0x2c16163a]
Te1 = [
    0xa5c66363, 0x84f87c7c, 0x99ee7777, 0x8df67b7b,
    0x0dfff2f2, 0xbdd66b6b, 0xb1de6f6f, 0x5491c5c5,
    0x50603030, 0x03020101, 0xa9ce6767, 0x7d562b2b,
    0x19e7fefe, 0x62b5d7d7, 0xe64dabab, 0x9aec7676,
    0x458fcaca, 0x9d1f8282, 0x4089c9c9, 0x87fa7d7d,
    0x15effafa, 0xebb25959, 0xc98e4747, 0x0bfbf0f0,
    0xec41adad, 0x67b3d4d4, 0xfd5fa2a2, 0xea45afaf,
    0xbf239c9c, 0xf753a4a4, 0x96e47272, 0x5b9bc0c0,
    0xc275b7b7, 0x1ce1fdfd, 0xae3d9393, 0x6a4c2626,
    0x5a6c3636, 0x417e3f3f, 0x02f5f7f7, 0x4f83cccc,
    0x5c683434, 0xf451a5a5, 0x34d1e5e5, 0x08f9f1f1,
    0x93e27171, 0x73abd8d8, 0x53623131, 0x3f2a1515,
    0x0c080404, 0x5295c7c7, 0x65462323, 0x5e9dc3c3,
    0x28301818, 0xa1379696, 0x0f0a0505, 0xb52f9a9a,
    0x090e0707, 0x36241212, 0x9b1b8080, 0x3ddfe2e2,
    0x26cdebeb, 0x694e2727, 0xcd7fb2b2, 0x9fea7575,
    0x1b120909, 0x9e1d8383, 0x74582c2c, 0x2e341a1a,
    0x2d361b1b, 0xb2dc6e6e, 0xeeb45a5a, 0xfb5ba0a0,
    0xf6a45252, 0x4d763b3b, 0x61b7d6d6, 0xce7db3b3,
    0x7b522929, 0x3edde3e3, 0x715e2f2f, 0x97138484,
    0xf5a65353, 0x68b9d1d1, 0x00000000, 0x2cc1eded,
    0x60402020, 0x1fe3fcfc, 0xc879b1b1, 0xedb65b5b,
    0xbed46a6a, 0x468dcbcb, 0xd967bebe, 0x4b723939,
    0xde944a4a, 0xd4984c4c, 0xe8b05858, 0x4a85cfcf,
    0x6bbbd0d0, 0x2ac5efef, 0xe54faaaa, 0x16edfbfb,
    0xc5864343, 0xd79a4d4d, 0x55663333, 0x94118585,
    0xcf8a4545, 0x10e9f9f9, 0x06040202, 0x81fe7f7f,
    0xf0a05050, 0x44783c3c, 0xba259f9f, 0xe34ba8a8,
    0xf3a25151, 0xfe5da3a3, 0xc0804040, 0x8a058f8f,
    0xad3f9292, 0xbc219d9d, 0x48703838, 0x04f1f5f5,
    0xdf63bcbc, 0xc177b6b6, 0x75afdada, 0x63422121,
    0x30201010, 0x1ae5ffff, 0x0efdf3f3, 0x6dbfd2d2,
    0x4c81cdcd, 0x14180c0c, 0x35261313, 0x2fc3ecec,
    0xe1be5f5f, 0xa2359797, 0xcc884444, 0x392e1717,
    0x5793c4c4, 0xf255a7a7, 0x82fc7e7e, 0x477a3d3d,
    0xacc86464, 0xe7ba5d5d, 0x2b321919, 0x95e67373,
    0xa0c06060, 0x98198181, 0xd19e4f4f, 0x7fa3dcdc,
    0x66442222, 0x7e542a2a, 0xab3b9090, 0x830b8888,
    0xca8c4646, 0x29c7eeee, 0xd36bb8b8, 0x3c281414,
    0x79a7dede, 0xe2bc5e5e, 0x1d160b0b, 0x76addbdb,
    0x3bdbe0e0, 0x56643232, 0x4e743a3a, 0x1e140a0a,
    0xdb924949, 0x0a0c0606, 0x6c482424, 0xe4b85c5c,
    0x5d9fc2c2, 0x6ebdd3d3, 0xef43acac, 0xa6c46262,
    0xa8399191, 0xa4319595, 0x37d3e4e4, 0x8bf27979,
    0x32d5e7e7, 0x438bc8c8, 0x596e3737, 0xb7da6d6d,
    0x8c018d8d, 0x64b1d5d5, 0xd29c4e4e, 0xe049a9a9,
    0xb4d86c6c, 0xfaac5656, 0x07f3f4f4, 0x25cfeaea,
    0xafca6565, 0x8ef47a7a, 0xe947aeae, 0x18100808,
    0xd56fbaba, 0x88f07878, 0x6f4a2525, 0x725c2e2e,
    0x24381c1c, 0xf157a6a6, 0xc773b4b4, 0x5197c6c6,
    0x23cbe8e8, 0x7ca1dddd, 0x9ce87474, 0x213e1f1f,
    0xdd964b4b, 0xdc61bdbd, 0x860d8b8b, 0x850f8a8a,
    0x90e07070, 0x427c3e3e, 0xc471b5b5, 0xaacc6666,
    0xd8904848, 0x05060303, 0x01f7f6f6, 0x121c0e0e,
    0xa3c26161, 0x5f6a3535, 0xf9ae5757, 0xd069b9b9,
    0x91178686, 0x5899c1c1, 0x273a1d1d, 0xb9279e9e,
    0x38d9e1e1, 0x13ebf8f8, 0xb32b9898, 0x33221111,
    0xbbd26969, 0x70a9d9d9, 0x89078e8e, 0xa7339494,
    0xb62d9b9b, 0x223c1e1e, 0x92158787, 0x20c9e9e9,
    0x4987cece, 0xffaa5555, 0x78502828, 0x7aa5dfdf,
    0x8f038c8c, 0xf859a1a1, 0x80098989, 0x171a0d0d,
    0xda65bfbf, 0x31d7e6e6, 0xc6844242, 0xb8d06868,
    0xc3824141, 0xb0299999, 0x775a2d2d, 0x111e0f0f,
    0xcb7bb0b0, 0xfca85454, 0xd66dbbbb, 0x3a2c1616]
Te2 = [
    0x63a5c663, 0x7c84f87c, 0x7799ee77, 0x7b8df67b,
    0xf20dfff2, 0x6bbdd66b, 0x6fb1de6f, 0xc55491c5,
    0x30506030, 0x01030201, 0x67a9ce67, 0x2b7d562b,
    0xfe19e7fe, 0xd762b5d7, 0xabe64dab, 0x769aec76,
    0xca458fca, 0x829d1f82, 0xc94089c9, 0x7d87fa7d,
    0xfa15effa, 0x59ebb259, 0x47c98e47, 0xf00bfbf0,
    0xadec41ad, 0xd467b3d4, 0xa2fd5fa2, 0xafea45af,
    0x9cbf239c, 0xa4f753a4, 0x7296e472, 0xc05b9bc0,
    0xb7c275b7, 0xfd1ce1fd, 0x93ae3d93, 0x266a4c26,
    0x365a6c36, 0x3f417e3f, 0xf702f5f7, 0xcc4f83cc,
    0x345c6834, 0xa5f451a5, 0xe534d1e5, 0xf108f9f1,
    0x7193e271, 0xd873abd8, 0x31536231, 0x153f2a15,
    0x040c0804, 0xc75295c7, 0x23654623, 0xc35e9dc3,
    0x18283018, 0x96a13796, 0x050f0a05, 0x9ab52f9a,
    0x07090e07, 0x12362412, 0x809b1b80, 0xe23ddfe2,
    0xeb26cdeb, 0x27694e27, 0xb2cd7fb2, 0x759fea75,
    0x091b1209, 0x839e1d83, 0x2c74582c, 0x1a2e341a,
    0x1b2d361b, 0x6eb2dc6e, 0x5aeeb45a, 0xa0fb5ba0,
    0x52f6a452, 0x3b4d763b, 0xd661b7d6, 0xb3ce7db3,
    0x297b5229, 0xe33edde3, 0x2f715e2f, 0x84971384,
    0x53f5a653, 0xd168b9d1, 0x00000000, 0xed2cc1ed,
    0x20604020, 0xfc1fe3fc, 0xb1c879b1, 0x5bedb65b,
    0x6abed46a, 0xcb468dcb, 0xbed967be, 0x394b7239,
    0x4ade944a, 0x4cd4984c, 0x58e8b058, 0xcf4a85cf,
    0xd06bbbd0, 0xef2ac5ef, 0xaae54faa, 0xfb16edfb,
    0x43c58643, 0x4dd79a4d, 0x33556633, 0x85941185,
    0x45cf8a45, 0xf910e9f9, 0x02060402, 0x7f81fe7f,
    0x50f0a050, 0x3c44783c, 0x9fba259f, 0xa8e34ba8,
    0x51f3a251, 0xa3fe5da3, 0x40c08040, 0x8f8a058f,
    0x92ad3f92, 0x9dbc219d, 0x38487038, 0xf504f1f5,
    0xbcdf63bc, 0xb6c177b6, 0xda75afda, 0x21634221,
    0x10302010, 0xff1ae5ff, 0xf30efdf3, 0xd26dbfd2,
    0xcd4c81cd, 0x0c14180c, 0x13352613, 0xec2fc3ec,
    0x5fe1be5f, 0x97a23597, 0x44cc8844, 0x17392e17,
    0xc45793c4, 0xa7f255a7, 0x7e82fc7e, 0x3d477a3d,
    0x64acc864, 0x5de7ba5d, 0x192b3219, 0x7395e673,
    0x60a0c060, 0x81981981, 0x4fd19e4f, 0xdc7fa3dc,
    0x22664422, 0x2a7e542a, 0x90ab3b90, 0x88830b88,
    0x46ca8c46, 0xee29c7ee, 0xb8d36bb8, 0x143c2814,
    0xde79a7de, 0x5ee2bc5e, 0x0b1d160b, 0xdb76addb,
    0xe03bdbe0, 0x32566432, 0x3a4e743a, 0x0a1e140a,
    0x49db9249, 0x060a0c06, 0x246c4824, 0x5ce4b85c,
    0xc25d9fc2, 0xd36ebdd3, 0xacef43ac, 0x62a6c462,
    0x91a83991, 0x95a43195, 0xe437d3e4, 0x798bf279,
    0xe732d5e7, 0xc8438bc8, 0x37596e37, 0x6db7da6d,
    0x8d8c018d, 0xd564b1d5, 0x4ed29c4e, 0xa9e049a9,
    0x6cb4d86c, 0x56faac56, 0xf407f3f4, 0xea25cfea,
    0x65afca65, 0x7a8ef47a, 0xaee947ae, 0x08181008,
    0xbad56fba, 0x7888f078, 0x256f4a25, 0x2e725c2e,
    0x1c24381c, 0xa6f157a6, 0xb4c773b4, 0xc65197c6,
    0xe823cbe8, 0xdd7ca1dd, 0x749ce874, 0x1f213e1f,
    0x4bdd964b, 0xbddc61bd, 0x8b860d8b, 0x8a850f8a,
    0x7090e070, 0x3e427c3e, 0xb5c471b5, 0x66aacc66,
    0x48d89048, 0x03050603, 0xf601f7f6, 0x0e121c0e,
    0x61a3c261, 0x355f6a35, 0x57f9ae57, 0xb9d069b9,
    0x86911786, 0xc15899c1, 0x1d273a1d, 0x9eb9279e,
    0xe138d9e1, 0xf813ebf8, 0x98b32b98, 0x11332211,
    0x69bbd269, 0xd970a9d9, 0x8e89078e, 0x94a73394,
    0x9bb62d9b, 0x1e223c1e, 0x87921587, 0xe920c9e9,
    0xce4987ce, 0x55ffaa55, 0x28785028, 0xdf7aa5df,
    0x8c8f038c, 0xa1f859a1, 0x89800989, 0x0d171a0d,
    0xbfda65bf, 0xe631d7e6, 0x42c68442, 0x68b8d068,
    0x41c38241, 0x99b02999, 0x2d775a2d, 0x0f111e0f,
    0xb0cb7bb0, 0x54fca854, 0xbbd66dbb, 0x163a2c16]
Te3 = [
    0x6363a5c6, 0x7c7c84f8, 0x777799ee, 0x7b7b8df6,
    0xf2f20dff, 0x6b6bbdd6, 0x6f6fb1de, 0xc5c55491,
    0x30305060, 0x01010302, 0x6767a9ce, 0x2b2b7d56,
    0xfefe19e7, 0xd7d762b5, 0xababe64d, 0x76769aec,
    0xcaca458f, 0x82829d1f, 0xc9c94089, 0x7d7d87fa,
    0xfafa15ef, 0x5959ebb2, 0x4747c98e, 0xf0f00bfb,
    0xadadec41, 0xd4d467b3, 0xa2a2fd5f, 0xafafea45,
    0x9c9cbf23, 0xa4a4f753, 0x727296e4, 0xc0c05b9b,
    0xb7b7c275, 0xfdfd1ce1, 0x9393ae3d, 0x26266a4c,
    0x36365a6c, 0x3f3f417e, 0xf7f702f5, 0xcccc4f83,
    0x34345c68, 0xa5a5f451, 0xe5e534d1, 0xf1f108f9,
    0x717193e2, 0xd8d873ab, 0x31315362, 0x15153f2a,
    0x04040c08, 0xc7c75295, 0x23236546, 0xc3c35e9d,
    0x18182830, 0x9696a137, 0x05050f0a, 0x9a9ab52f,
    0x0707090e, 0x12123624, 0x80809b1b, 0xe2e23ddf,
    0xebeb26cd, 0x2727694e, 0xb2b2cd7f, 0x75759fea,
    0x09091b12, 0x83839e1d, 0x2c2c7458, 0x1a1a2e34,
    0x1b1b2d36, 0x6e6eb2dc, 0x5a5aeeb4, 0xa0a0fb5b,
    0x5252f6a4, 0x3b3b4d76, 0xd6d661b7, 0xb3b3ce7d,
    0x29297b52, 0xe3e33edd, 0x2f2f715e, 0x84849713,
    0x5353f5a6, 0xd1d168b9, 0x00000000, 0xeded2cc1,
    0x20206040, 0xfcfc1fe3, 0xb1b1c879, 0x5b5bedb6,
    0x6a6abed4, 0xcbcb468d, 0xbebed967, 0x39394b72,
    0x4a4ade94, 0x4c4cd498, 0x5858e8b0, 0xcfcf4a85,
    0xd0d06bbb, 0xefef2ac5, 0xaaaae54f, 0xfbfb16ed,
    0x4343c586, 0x4d4dd79a, 0x33335566, 0x85859411,
    0x4545cf8a, 0xf9f910e9, 0x02020604, 0x7f7f81fe,
    0x5050f0a0, 0x3c3c4478, 0x9f9fba25, 0xa8a8e34b,
    0x5151f3a2, 0xa3a3fe5d, 0x4040c080, 0x8f8f8a05,
    0x9292ad3f, 0x9d9dbc21, 0x38384870, 0xf5f504f1,
    0xbcbcdf63, 0xb6b6c177, 0xdada75af, 0x21216342,
    0x10103020, 0xffff1ae5, 0xf3f30efd, 0xd2d26dbf,
    0xcdcd4c81, 0x0c0c1418, 0x13133526, 0xecec2fc3,
    0x5f5fe1be, 0x9797a235, 0x4444cc88, 0x1717392e,
    0xc4c45793, 0xa7a7f255, 0x7e7e82fc, 0x3d3d477a,
    0x6464acc8, 0x5d5de7ba, 0x19192b32, 0x737395e6,
    0x6060a0c0, 0x81819819, 0x4f4fd19e, 0xdcdc7fa3,
    0x22226644, 0x2a2a7e54, 0x9090ab3b, 0x8888830b,
    0x4646ca8c, 0xeeee29c7, 0xb8b8d36b, 0x14143c28,
    0xdede79a7, 0x5e5ee2bc, 0x0b0b1d16, 0xdbdb76ad,
    0xe0e03bdb, 0x32325664, 0x3a3a4e74, 0x0a0a1e14,
    0x4949db92, 0x06060a0c, 0x24246c48, 0x5c5ce4b8,
    0xc2c25d9f, 0xd3d36ebd, 0xacacef43, 0x6262a6c4,
    0x9191a839, 0x9595a431, 0xe4e437d3, 0x79798bf2,
    0xe7e732d5, 0xc8c8438b, 0x3737596e, 0x6d6db7da,
    0x8d8d8c01, 0xd5d564b1, 0x4e4ed29c, 0xa9a9e049,
    0x6c6cb4d8, 0x5656faac, 0xf4f407f3, 0xeaea25cf,
    0x6565afca, 0x7a7a8ef4, 0xaeaee947, 0x08081810,
    0xbabad56f, 0x787888f0, 0x25256f4a, 0x2e2e725c,
    0x1c1c2438, 0xa6a6f157, 0xb4b4c773, 0xc6c65197,
    0xe8e823cb, 0xdddd7ca1, 0x74749ce8, 0x1f1f213e,
    0x4b4bdd96, 0xbdbddc61, 0x8b8b860d, 0x8a8a850f,
    0x707090e0, 0x3e3e427c, 0xb5b5c471, 0x6666aacc,
    0x4848d890, 0x03030506, 0xf6f601f7, 0x0e0e121c,
    0x6161a3c2, 0x35355f6a, 0x5757f9ae, 0xb9b9d069,
    0x86869117, 0xc1c15899, 0x1d1d273a, 0x9e9eb927,
    0xe1e138d9, 0xf8f813eb, 0x9898b32b, 0x11113322,
    0x6969bbd2, 0xd9d970a9, 0x8e8e8907, 0x9494a733,
    0x9b9bb62d, 0x1e1e223c, 0x87879215, 0xe9e920c9,
    0xcece4987, 0x5555ffaa, 0x28287850, 0xdfdf7aa5,
    0x8c8c8f03, 0xa1a1f859, 0x89898009, 0x0d0d171a,
    0xbfbfda65, 0xe6e631d7, 0x4242c684, 0x6868b8d0,
    0x4141c382, 0x9999b029, 0x2d2d775a, 0x0f0f111e,
    0xb0b0cb7b, 0x5454fca8, 0xbbbbd66d, 0x16163a2c]
Te4 = [
    0x63636363, 0x7c7c7c7c, 0x77777777, 0x7b7b7b7b,
    0xf2f2f2f2, 0x6b6b6b6b, 0x6f6f6f6f, 0xc5c5c5c5,
    0x30303030, 0x01010101, 0x67676767, 0x2b2b2b2b,
    0xfefefefe, 0xd7d7d7d7, 0xabababab, 0x76767676,
    0xcacacaca, 0x82828282, 0xc9c9c9c9, 0x7d7d7d7d,
    0xfafafafa, 0x59595959, 0x47474747, 0xf0f0f0f0,
    0xadadadad, 0xd4d4d4d4, 0xa2a2a2a2, 0xafafafaf,
    0x9c9c9c9c, 0xa4a4a4a4, 0x72727272, 0xc0c0c0c0,
    0xb7b7b7b7, 0xfdfdfdfd, 0x93939393, 0x26262626,
    0x36363636, 0x3f3f3f3f, 0xf7f7f7f7, 0xcccccccc,
    0x34343434, 0xa5a5a5a5, 0xe5e5e5e5, 0xf1f1f1f1,
    0x71717171, 0xd8d8d8d8, 0x31313131, 0x15151515,
    0x04040404, 0xc7c7c7c7, 0x23232323, 0xc3c3c3c3,
    0x18181818, 0x96969696, 0x05050505, 0x9a9a9a9a,
    0x07070707, 0x12121212, 0x80808080, 0xe2e2e2e2,
    0xebebebeb, 0x27272727, 0xb2b2b2b2, 0x75757575,
    0x09090909, 0x83838383, 0x2c2c2c2c, 0x1a1a1a1a,
    0x1b1b1b1b, 0x6e6e6e6e, 0x5a5a5a5a, 0xa0a0a0a0,
    0x52525252, 0x3b3b3b3b, 0xd6d6d6d6, 0xb3b3b3b3,
    0x29292929, 0xe3e3e3e3, 0x2f2f2f2f, 0x84848484,
    0x53535353, 0xd1d1d1d1, 0x00000000, 0xedededed,
    0x20202020, 0xfcfcfcfc, 0xb1b1b1b1, 0x5b5b5b5b,
    0x6a6a6a6a, 0xcbcbcbcb, 0xbebebebe, 0x39393939,
    0x4a4a4a4a, 0x4c4c4c4c, 0x58585858, 0xcfcfcfcf,
    0xd0d0d0d0, 0xefefefef, 0xaaaaaaaa, 0xfbfbfbfb,
    0x43434343, 0x4d4d4d4d, 0x33333333, 0x85858585,
    0x45454545, 0xf9f9f9f9, 0x02020202, 0x7f7f7f7f,
    0x50505050, 0x3c3c3c3c, 0x9f9f9f9f, 0xa8a8a8a8,
    0x51515151, 0xa3a3a3a3, 0x40404040, 0x8f8f8f8f,
    0x92929292, 0x9d9d9d9d, 0x38383838, 0xf5f5f5f5,
    0xbcbcbcbc, 0xb6b6b6b6, 0xdadadada, 0x21212121,
    0x10101010, 0xffffffff, 0xf3f3f3f3, 0xd2d2d2d2,
    0xcdcdcdcd, 0x0c0c0c0c, 0x13131313, 0xecececec,
    0x5f5f5f5f, 0x97979797, 0x44444444, 0x17171717,
    0xc4c4c4c4, 0xa7a7a7a7, 0x7e7e7e7e, 0x3d3d3d3d,
    0x64646464, 0x5d5d5d5d, 0x19191919, 0x73737373,
    0x60606060, 0x81818181, 0x4f4f4f4f, 0xdcdcdcdc,
    0x22222222, 0x2a2a2a2a, 0x90909090, 0x88888888,
    0x46464646, 0xeeeeeeee, 0xb8b8b8b8, 0x14141414,
    0xdededede, 0x5e5e5e5e, 0x0b0b0b0b, 0xdbdbdbdb,
    0xe0e0e0e0, 0x32323232, 0x3a3a3a3a, 0x0a0a0a0a,
    0x49494949, 0x06060606, 0x24242424, 0x5c5c5c5c,
    0xc2c2c2c2, 0xd3d3d3d3, 0xacacacac, 0x62626262,
    0x91919191, 0x95959595, 0xe4e4e4e4, 0x79797979,
    0xe7e7e7e7, 0xc8c8c8c8, 0x37373737, 0x6d6d6d6d,
    0x8d8d8d8d, 0xd5d5d5d5, 0x4e4e4e4e, 0xa9a9a9a9,
    0x6c6c6c6c, 0x56565656, 0xf4f4f4f4, 0xeaeaeaea,
    0x65656565, 0x7a7a7a7a, 0xaeaeaeae, 0x08080808,
    0xbabababa, 0x78787878, 0x25252525, 0x2e2e2e2e,
    0x1c1c1c1c, 0xa6a6a6a6, 0xb4b4b4b4, 0xc6c6c6c6,
    0xe8e8e8e8, 0xdddddddd, 0x74747474, 0x1f1f1f1f,
    0x4b4b4b4b, 0xbdbdbdbd, 0x8b8b8b8b, 0x8a8a8a8a,
    0x70707070, 0x3e3e3e3e, 0xb5b5b5b5, 0x66666666,
    0x48484848, 0x03030303, 0xf6f6f6f6, 0x0e0e0e0e,
    0x61616161, 0x35353535, 0x57575757, 0xb9b9b9b9,
    0x86868686, 0xc1c1c1c1, 0x1d1d1d1d, 0x9e9e9e9e,
    0xe1e1e1e1, 0xf8f8f8f8, 0x98989898, 0x11111111,
    0x69696969, 0xd9d9d9d9, 0x8e8e8e8e, 0x94949494,
    0x9b9b9b9b, 0x1e1e1e1e, 0x87878787, 0xe9e9e9e9,
    0xcececece, 0x55555555, 0x28282828, 0xdfdfdfdf,
    0x8c8c8c8c, 0xa1a1a1a1, 0x89898989, 0x0d0d0d0d,
    0xbfbfbfbf, 0xe6e6e6e6, 0x42424242, 0x68686868,
    0x41414141, 0x99999999, 0x2d2d2d2d, 0x0f0f0f0f,
    0xb0b0b0b0, 0x54545454, 0xbbbbbbbb, 0x16161616]
Td0 = [
    0x51f4a750, 0x7e416553, 0x1a17a4c3, 0x3a275e96,
    0x3bab6bcb, 0x1f9d45f1, 0xacfa58ab, 0x4be30393,
    0x2030fa55, 0xad766df6, 0x88cc7691, 0xf5024c25,
    0x4fe5d7fc, 0xc52acbd7, 0x26354480, 0xb562a38f,
    0xdeb15a49, 0x25ba1b67, 0x45ea0e98, 0x5dfec0e1,
    0xc32f7502, 0x814cf012, 0x8d4697a3, 0x6bd3f9c6,
    0x038f5fe7, 0x15929c95, 0xbf6d7aeb, 0x955259da,
    0xd4be832d, 0x587421d3, 0x49e06929, 0x8ec9c844,
    0x75c2896a, 0xf48e7978, 0x99583e6b, 0x27b971dd,
    0xbee14fb6, 0xf088ad17, 0xc920ac66, 0x7dce3ab4,
    0x63df4a18, 0xe51a3182, 0x97513360, 0x62537f45,
    0xb16477e0, 0xbb6bae84, 0xfe81a01c, 0xf9082b94,
    0x70486858, 0x8f45fd19, 0x94de6c87, 0x527bf8b7,
    0xab73d323, 0x724b02e2, 0xe31f8f57, 0x6655ab2a,
    0xb2eb2807, 0x2fb5c203, 0x86c57b9a, 0xd33708a5,
    0x302887f2, 0x23bfa5b2, 0x02036aba, 0xed16825c,
    0x8acf1c2b, 0xa779b492, 0xf307f2f0, 0x4e69e2a1,
    0x65daf4cd, 0x0605bed5, 0xd134621f, 0xc4a6fe8a,
    0x342e539d, 0xa2f355a0, 0x058ae132, 0xa4f6eb75,
    0x0b83ec39, 0x4060efaa, 0x5e719f06, 0xbd6e1051,
    0x3e218af9, 0x96dd063d, 0xdd3e05ae, 0x4de6bd46,
    0x91548db5, 0x71c45d05, 0x0406d46f, 0x605015ff,
    0x1998fb24, 0xd6bde997, 0x894043cc, 0x67d99e77,
    0xb0e842bd, 0x07898b88, 0xe7195b38, 0x79c8eedb,
    0xa17c0a47, 0x7c420fe9, 0xf8841ec9, 0x00000000,
    0x09808683, 0x322bed48, 0x1e1170ac, 0x6c5a724e,
    0xfd0efffb, 0x0f853856, 0x3daed51e, 0x362d3927,
    0x0a0fd964, 0x685ca621, 0x9b5b54d1, 0x24362e3a,
    0x0c0a67b1, 0x9357e70f, 0xb4ee96d2, 0x1b9b919e,
    0x80c0c54f, 0x61dc20a2, 0x5a774b69, 0x1c121a16,
    0xe293ba0a, 0xc0a02ae5, 0x3c22e043, 0x121b171d,
    0x0e090d0b, 0xf28bc7ad, 0x2db6a8b9, 0x141ea9c8,
    0x57f11985, 0xaf75074c, 0xee99ddbb, 0xa37f60fd,
    0xf701269f, 0x5c72f5bc, 0x44663bc5, 0x5bfb7e34,
    0x8b432976, 0xcb23c6dc, 0xb6edfc68, 0xb8e4f163,
    0xd731dcca, 0x42638510, 0x13972240, 0x84c61120,
    0x854a247d, 0xd2bb3df8, 0xaef93211, 0xc729a16d,
    0x1d9e2f4b, 0xdcb230f3, 0x0d8652ec, 0x77c1e3d0,
    0x2bb3166c, 0xa970b999, 0x119448fa, 0x47e96422,
    0xa8fc8cc4, 0xa0f03f1a, 0x567d2cd8, 0x223390ef,
    0x87494ec7, 0xd938d1c1, 0x8ccaa2fe, 0x98d40b36,
    0xa6f581cf, 0xa57ade28, 0xdab78e26, 0x3fadbfa4,
    0x2c3a9de4, 0x5078920d, 0x6a5fcc9b, 0x547e4662,
    0xf68d13c2, 0x90d8b8e8, 0x2e39f75e, 0x82c3aff5,
    0x9f5d80be, 0x69d0937c, 0x6fd52da9, 0xcf2512b3,
    0xc8ac993b, 0x10187da7, 0xe89c636e, 0xdb3bbb7b,
    0xcd267809, 0x6e5918f4, 0xec9ab701, 0x834f9aa8,
    0xe6956e65, 0xaaffe67e, 0x21bccf08, 0xef15e8e6,
    0xbae79bd9, 0x4a6f36ce, 0xea9f09d4, 0x29b07cd6,
    0x31a4b2af, 0x2a3f2331, 0xc6a59430, 0x35a266c0,
    0x744ebc37, 0xfc82caa6, 0xe090d0b0, 0x33a7d815,
    0xf104984a, 0x41ecdaf7, 0x7fcd500e, 0x1791f62f,
    0x764dd68d, 0x43efb04d, 0xccaa4d54, 0xe49604df,
    0x9ed1b5e3, 0x4c6a881b, 0xc12c1fb8, 0x4665517f,
    0x9d5eea04, 0x018c355d, 0xfa877473, 0xfb0b412e,
    0xb3671d5a, 0x92dbd252, 0xe9105633, 0x6dd64713,
    0x9ad7618c, 0x37a10c7a, 0x59f8148e, 0xeb133c89,
    0xcea927ee, 0xb761c935, 0xe11ce5ed, 0x7a47b13c,
    0x9cd2df59, 0x55f2733f, 0x1814ce79, 0x73c737bf,
    0x53f7cdea, 0x5ffdaa5b, 0xdf3d6f14, 0x7844db86,
    0xcaaff381, 0xb968c43e, 0x3824342c, 0xc2a3405f,
    0x161dc372, 0xbce2250c, 0x283c498b, 0xff0d9541,
    0x39a80171, 0x080cb3de, 0xd8b4e49c, 0x6456c190,
    0x7bcb8461, 0xd532b670, 0x486c5c74, 0xd0b85742]
Td1 = [
    0x5051f4a7, 0x537e4165, 0xc31a17a4, 0x963a275e,
    0xcb3bab6b, 0xf11f9d45, 0xabacfa58, 0x934be303,
    0x552030fa, 0xf6ad766d, 0x9188cc76, 0x25f5024c,
    0xfc4fe5d7, 0xd7c52acb, 0x80263544, 0x8fb562a3,
    0x49deb15a, 0x6725ba1b, 0x9845ea0e, 0xe15dfec0,
    0x02c32f75, 0x12814cf0, 0xa38d4697, 0xc66bd3f9,
    0xe7038f5f, 0x9515929c, 0xebbf6d7a, 0xda955259,
    0x2dd4be83, 0xd3587421, 0x2949e069, 0x448ec9c8,
    0x6a75c289, 0x78f48e79, 0x6b99583e, 0xdd27b971,
    0xb6bee14f, 0x17f088ad, 0x66c920ac, 0xb47dce3a,
    0x1863df4a, 0x82e51a31, 0x60975133, 0x4562537f,
    0xe0b16477, 0x84bb6bae, 0x1cfe81a0, 0x94f9082b,
    0x58704868, 0x198f45fd, 0x8794de6c, 0xb7527bf8,
    0x23ab73d3, 0xe2724b02, 0x57e31f8f, 0x2a6655ab,
    0x07b2eb28, 0x032fb5c2, 0x9a86c57b, 0xa5d33708,
    0xf2302887, 0xb223bfa5, 0xba02036a, 0x5ced1682,
    0x2b8acf1c, 0x92a779b4, 0xf0f307f2, 0xa14e69e2,
    0xcd65daf4, 0xd50605be, 0x1fd13462, 0x8ac4a6fe,
    0x9d342e53, 0xa0a2f355, 0x32058ae1, 0x75a4f6eb,
    0x390b83ec, 0xaa4060ef, 0x065e719f, 0x51bd6e10,
    0xf93e218a, 0x3d96dd06, 0xaedd3e05, 0x464de6bd,
    0xb591548d, 0x0571c45d, 0x6f0406d4, 0xff605015,
    0x241998fb, 0x97d6bde9, 0xcc894043, 0x7767d99e,
    0xbdb0e842, 0x8807898b, 0x38e7195b, 0xdb79c8ee,
    0x47a17c0a, 0xe97c420f, 0xc9f8841e, 0x00000000,
    0x83098086, 0x48322bed, 0xac1e1170, 0x4e6c5a72,
    0xfbfd0eff, 0x560f8538, 0x1e3daed5, 0x27362d39,
    0x640a0fd9, 0x21685ca6, 0xd19b5b54, 0x3a24362e,
    0xb10c0a67, 0x0f9357e7, 0xd2b4ee96, 0x9e1b9b91,
    0x4f80c0c5, 0xa261dc20, 0x695a774b, 0x161c121a,
    0x0ae293ba, 0xe5c0a02a, 0x433c22e0, 0x1d121b17,
    0x0b0e090d, 0xadf28bc7, 0xb92db6a8, 0xc8141ea9,
    0x8557f119, 0x4caf7507, 0xbbee99dd, 0xfda37f60,
    0x9ff70126, 0xbc5c72f5, 0xc544663b, 0x345bfb7e,
    0x768b4329, 0xdccb23c6, 0x68b6edfc, 0x63b8e4f1,
    0xcad731dc, 0x10426385, 0x40139722, 0x2084c611,
    0x7d854a24, 0xf8d2bb3d, 0x11aef932, 0x6dc729a1,
    0x4b1d9e2f, 0xf3dcb230, 0xec0d8652, 0xd077c1e3,
    0x6c2bb316, 0x99a970b9, 0xfa119448, 0x2247e964,
    0xc4a8fc8c, 0x1aa0f03f, 0xd8567d2c, 0xef223390,
    0xc787494e, 0xc1d938d1, 0xfe8ccaa2, 0x3698d40b,
    0xcfa6f581, 0x28a57ade, 0x26dab78e, 0xa43fadbf,
    0xe42c3a9d, 0x0d507892, 0x9b6a5fcc, 0x62547e46,
    0xc2f68d13, 0xe890d8b8, 0x5e2e39f7, 0xf582c3af,
    0xbe9f5d80, 0x7c69d093, 0xa96fd52d, 0xb3cf2512,
    0x3bc8ac99, 0xa710187d, 0x6ee89c63, 0x7bdb3bbb,
    0x09cd2678, 0xf46e5918, 0x01ec9ab7, 0xa8834f9a,
    0x65e6956e, 0x7eaaffe6, 0x0821bccf, 0xe6ef15e8,
    0xd9bae79b, 0xce4a6f36, 0xd4ea9f09, 0xd629b07c,
    0xaf31a4b2, 0x312a3f23, 0x30c6a594, 0xc035a266,
    0x37744ebc, 0xa6fc82ca, 0xb0e090d0, 0x1533a7d8,
    0x4af10498, 0xf741ecda, 0x0e7fcd50, 0x2f1791f6,
    0x8d764dd6, 0x4d43efb0, 0x54ccaa4d, 0xdfe49604,
    0xe39ed1b5, 0x1b4c6a88, 0xb8c12c1f, 0x7f466551,
    0x049d5eea, 0x5d018c35, 0x73fa8774, 0x2efb0b41,
    0x5ab3671d, 0x5292dbd2, 0x33e91056, 0x136dd647,
    0x8c9ad761, 0x7a37a10c, 0x8e59f814, 0x89eb133c,
    0xeecea927, 0x35b761c9, 0xede11ce5, 0x3c7a47b1,
    0x599cd2df, 0x3f55f273, 0x791814ce, 0xbf73c737,
    0xea53f7cd, 0x5b5ffdaa, 0x14df3d6f, 0x867844db,
    0x81caaff3, 0x3eb968c4, 0x2c382434, 0x5fc2a340,
    0x72161dc3, 0x0cbce225, 0x8b283c49, 0x41ff0d95,
    0x7139a801, 0xde080cb3, 0x9cd8b4e4, 0x906456c1,
    0x617bcb84, 0x70d532b6, 0x74486c5c, 0x42d0b857]
Td2 = [
    0xa75051f4, 0x65537e41, 0xa4c31a17, 0x5e963a27,
    0x6bcb3bab, 0x45f11f9d, 0x58abacfa, 0x03934be3,
    0xfa552030, 0x6df6ad76, 0x769188cc, 0x4c25f502,
    0xd7fc4fe5, 0xcbd7c52a, 0x44802635, 0xa38fb562,
    0x5a49deb1, 0x1b6725ba, 0x0e9845ea, 0xc0e15dfe,
    0x7502c32f, 0xf012814c, 0x97a38d46, 0xf9c66bd3,
    0x5fe7038f, 0x9c951592, 0x7aebbf6d, 0x59da9552,
    0x832dd4be, 0x21d35874, 0x692949e0, 0xc8448ec9,
    0x896a75c2, 0x7978f48e, 0x3e6b9958, 0x71dd27b9,
    0x4fb6bee1, 0xad17f088, 0xac66c920, 0x3ab47dce,
    0x4a1863df, 0x3182e51a, 0x33609751, 0x7f456253,
    0x77e0b164, 0xae84bb6b, 0xa01cfe81, 0x2b94f908,
    0x68587048, 0xfd198f45, 0x6c8794de, 0xf8b7527b,
    0xd323ab73, 0x02e2724b, 0x8f57e31f, 0xab2a6655,
    0x2807b2eb, 0xc2032fb5, 0x7b9a86c5, 0x08a5d337,
    0x87f23028, 0xa5b223bf, 0x6aba0203, 0x825ced16,
    0x1c2b8acf, 0xb492a779, 0xf2f0f307, 0xe2a14e69,
    0xf4cd65da, 0xbed50605, 0x621fd134, 0xfe8ac4a6,
    0x539d342e, 0x55a0a2f3, 0xe132058a, 0xeb75a4f6,
    0xec390b83, 0xefaa4060, 0x9f065e71, 0x1051bd6e,
    0x8af93e21, 0x063d96dd, 0x05aedd3e, 0xbd464de6,
    0x8db59154, 0x5d0571c4, 0xd46f0406, 0x15ff6050,
    0xfb241998, 0xe997d6bd, 0x43cc8940, 0x9e7767d9,
    0x42bdb0e8, 0x8b880789, 0x5b38e719, 0xeedb79c8,
    0x0a47a17c, 0x0fe97c42, 0x1ec9f884, 0x00000000,
    0x86830980, 0xed48322b, 0x70ac1e11, 0x724e6c5a,
    0xfffbfd0e, 0x38560f85, 0xd51e3dae, 0x3927362d,
    0xd9640a0f, 0xa621685c, 0x54d19b5b, 0x2e3a2436,
    0x67b10c0a, 0xe70f9357, 0x96d2b4ee, 0x919e1b9b,
    0xc54f80c0, 0x20a261dc, 0x4b695a77, 0x1a161c12,
    0xba0ae293, 0x2ae5c0a0, 0xe0433c22, 0x171d121b,
    0x0d0b0e09, 0xc7adf28b, 0xa8b92db6, 0xa9c8141e,
    0x198557f1, 0x074caf75, 0xddbbee99, 0x60fda37f,
    0x269ff701, 0xf5bc5c72, 0x3bc54466, 0x7e345bfb,
    0x29768b43, 0xc6dccb23, 0xfc68b6ed, 0xf163b8e4,
    0xdccad731, 0x85104263, 0x22401397, 0x112084c6,
    0x247d854a, 0x3df8d2bb, 0x3211aef9, 0xa16dc729,
    0x2f4b1d9e, 0x30f3dcb2, 0x52ec0d86, 0xe3d077c1,
    0x166c2bb3, 0xb999a970, 0x48fa1194, 0x642247e9,
    0x8cc4a8fc, 0x3f1aa0f0, 0x2cd8567d, 0x90ef2233,
    0x4ec78749, 0xd1c1d938, 0xa2fe8cca, 0x0b3698d4,
    0x81cfa6f5, 0xde28a57a, 0x8e26dab7, 0xbfa43fad,
    0x9de42c3a, 0x920d5078, 0xcc9b6a5f, 0x4662547e,
    0x13c2f68d, 0xb8e890d8, 0xf75e2e39, 0xaff582c3,
    0x80be9f5d, 0x937c69d0, 0x2da96fd5, 0x12b3cf25,
    0x993bc8ac, 0x7da71018, 0x636ee89c, 0xbb7bdb3b,
    0x7809cd26, 0x18f46e59, 0xb701ec9a, 0x9aa8834f,
    0x6e65e695, 0xe67eaaff, 0xcf0821bc, 0xe8e6ef15,
    0x9bd9bae7, 0x36ce4a6f, 0x09d4ea9f, 0x7cd629b0,
    0xb2af31a4, 0x23312a3f, 0x9430c6a5, 0x66c035a2,
    0xbc37744e, 0xcaa6fc82, 0xd0b0e090, 0xd81533a7,
    0x984af104, 0xdaf741ec, 0x500e7fcd, 0xf62f1791,
    0xd68d764d, 0xb04d43ef, 0x4d54ccaa, 0x04dfe496,
    0xb5e39ed1, 0x881b4c6a, 0x1fb8c12c, 0x517f4665,
    0xea049d5e, 0x355d018c, 0x7473fa87, 0x412efb0b,
    0x1d5ab367, 0xd25292db, 0x5633e910, 0x47136dd6,
    0x618c9ad7, 0x0c7a37a1, 0x148e59f8, 0x3c89eb13,
    0x27eecea9, 0xc935b761, 0xe5ede11c, 0xb13c7a47,
    0xdf599cd2, 0x733f55f2, 0xce791814, 0x37bf73c7,
    0xcdea53f7, 0xaa5b5ffd, 0x6f14df3d, 0xdb867844,
    0xf381caaf, 0xc43eb968, 0x342c3824, 0x405fc2a3,
    0xc372161d, 0x250cbce2, 0x498b283c, 0x9541ff0d,
    0x017139a8, 0xb3de080c, 0xe49cd8b4, 0xc1906456,
    0x84617bcb, 0xb670d532, 0x5c74486c, 0x5742d0b8]
Td3 = [
    0xf4a75051, 0x4165537e, 0x17a4c31a, 0x275e963a,
    0xab6bcb3b, 0x9d45f11f, 0xfa58abac, 0xe303934b,
    0x30fa5520, 0x766df6ad, 0xcc769188, 0x024c25f5,
    0xe5d7fc4f, 0x2acbd7c5, 0x35448026, 0x62a38fb5,
    0xb15a49de, 0xba1b6725, 0xea0e9845, 0xfec0e15d,
    0x2f7502c3, 0x4cf01281, 0x4697a38d, 0xd3f9c66b,
    0x8f5fe703, 0x929c9515, 0x6d7aebbf, 0x5259da95,
    0xbe832dd4, 0x7421d358, 0xe0692949, 0xc9c8448e,
    0xc2896a75, 0x8e7978f4, 0x583e6b99, 0xb971dd27,
    0xe14fb6be, 0x88ad17f0, 0x20ac66c9, 0xce3ab47d,
    0xdf4a1863, 0x1a3182e5, 0x51336097, 0x537f4562,
    0x6477e0b1, 0x6bae84bb, 0x81a01cfe, 0x082b94f9,
    0x48685870, 0x45fd198f, 0xde6c8794, 0x7bf8b752,
    0x73d323ab, 0x4b02e272, 0x1f8f57e3, 0x55ab2a66,
    0xeb2807b2, 0xb5c2032f, 0xc57b9a86, 0x3708a5d3,
    0x2887f230, 0xbfa5b223, 0x036aba02, 0x16825ced,
    0xcf1c2b8a, 0x79b492a7, 0x07f2f0f3, 0x69e2a14e,
    0xdaf4cd65, 0x05bed506, 0x34621fd1, 0xa6fe8ac4,
    0x2e539d34, 0xf355a0a2, 0x8ae13205, 0xf6eb75a4,
    0x83ec390b, 0x60efaa40, 0x719f065e, 0x6e1051bd,
    0x218af93e, 0xdd063d96, 0x3e05aedd, 0xe6bd464d,
    0x548db591, 0xc45d0571, 0x06d46f04, 0x5015ff60,
    0x98fb2419, 0xbde997d6, 0x4043cc89, 0xd99e7767,
    0xe842bdb0, 0x898b8807, 0x195b38e7, 0xc8eedb79,
    0x7c0a47a1, 0x420fe97c, 0x841ec9f8, 0x00000000,
    0x80868309, 0x2bed4832, 0x1170ac1e, 0x5a724e6c,
    0x0efffbfd, 0x8538560f, 0xaed51e3d, 0x2d392736,
    0x0fd9640a, 0x5ca62168, 0x5b54d19b, 0x362e3a24,
    0x0a67b10c, 0x57e70f93, 0xee96d2b4, 0x9b919e1b,
    0xc0c54f80, 0xdc20a261, 0x774b695a, 0x121a161c,
    0x93ba0ae2, 0xa02ae5c0, 0x22e0433c, 0x1b171d12,
    0x090d0b0e, 0x8bc7adf2, 0xb6a8b92d, 0x1ea9c814,
    0xf1198557, 0x75074caf, 0x99ddbbee, 0x7f60fda3,
    0x01269ff7, 0x72f5bc5c, 0x663bc544, 0xfb7e345b,
    0x4329768b, 0x23c6dccb, 0xedfc68b6, 0xe4f163b8,
    0x31dccad7, 0x63851042, 0x97224013, 0xc6112084,
    0x4a247d85, 0xbb3df8d2, 0xf93211ae, 0x29a16dc7,
    0x9e2f4b1d, 0xb230f3dc, 0x8652ec0d, 0xc1e3d077,
    0xb3166c2b, 0x70b999a9, 0x9448fa11, 0xe9642247,
    0xfc8cc4a8, 0xf03f1aa0, 0x7d2cd856, 0x3390ef22,
    0x494ec787, 0x38d1c1d9, 0xcaa2fe8c, 0xd40b3698,
    0xf581cfa6, 0x7ade28a5, 0xb78e26da, 0xadbfa43f,
    0x3a9de42c, 0x78920d50, 0x5fcc9b6a, 0x7e466254,
    0x8d13c2f6, 0xd8b8e890, 0x39f75e2e, 0xc3aff582,
    0x5d80be9f, 0xd0937c69, 0xd52da96f, 0x2512b3cf,
    0xac993bc8, 0x187da710, 0x9c636ee8, 0x3bbb7bdb,
    0x267809cd, 0x5918f46e, 0x9ab701ec, 0x4f9aa883,
    0x956e65e6, 0xffe67eaa, 0xbccf0821, 0x15e8e6ef,
    0xe79bd9ba, 0x6f36ce4a, 0x9f09d4ea, 0xb07cd629,
    0xa4b2af31, 0x3f23312a, 0xa59430c6, 0xa266c035,
    0x4ebc3774, 0x82caa6fc, 0x90d0b0e0, 0xa7d81533,
    0x04984af1, 0xecdaf741, 0xcd500e7f, 0x91f62f17,
    0x4dd68d76, 0xefb04d43, 0xaa4d54cc, 0x9604dfe4,
    0xd1b5e39e, 0x6a881b4c, 0x2c1fb8c1, 0x65517f46,
    0x5eea049d, 0x8c355d01, 0x877473fa, 0x0b412efb,
    0x671d5ab3, 0xdbd25292, 0x105633e9, 0xd647136d,
    0xd7618c9a, 0xa10c7a37, 0xf8148e59, 0x133c89eb,
    0xa927eece, 0x61c935b7, 0x1ce5ede1, 0x47b13c7a,
    0xd2df599c, 0xf2733f55, 0x14ce7918, 0xc737bf73,
    0xf7cdea53, 0xfdaa5b5f, 0x3d6f14df, 0x44db8678,
    0xaff381ca, 0x68c43eb9, 0x24342c38, 0xa3405fc2,
    0x1dc37216, 0xe2250cbc, 0x3c498b28, 0x0d9541ff,
    0xa8017139, 0x0cb3de08, 0xb4e49cd8, 0x56c19064,
    0xcb84617b, 0x32b670d5, 0x6c5c7448, 0xb85742d0]
Td4 = [
    0x52525252, 0x09090909, 0x6a6a6a6a, 0xd5d5d5d5,
    0x30303030, 0x36363636, 0xa5a5a5a5, 0x38383838,
    0xbfbfbfbf, 0x40404040, 0xa3a3a3a3, 0x9e9e9e9e,
    0x81818181, 0xf3f3f3f3, 0xd7d7d7d7, 0xfbfbfbfb,
    0x7c7c7c7c, 0xe3e3e3e3, 0x39393939, 0x82828282,
    0x9b9b9b9b, 0x2f2f2f2f, 0xffffffff, 0x87878787,
    0x34343434, 0x8e8e8e8e, 0x43434343, 0x44444444,
    0xc4c4c4c4, 0xdededede, 0xe9e9e9e9, 0xcbcbcbcb,
    0x54545454, 0x7b7b7b7b, 0x94949494, 0x32323232,
    0xa6a6a6a6, 0xc2c2c2c2, 0x23232323, 0x3d3d3d3d,
    0xeeeeeeee, 0x4c4c4c4c, 0x95959595, 0x0b0b0b0b,
    0x42424242, 0xfafafafa, 0xc3c3c3c3, 0x4e4e4e4e,
    0x08080808, 0x2e2e2e2e, 0xa1a1a1a1, 0x66666666,
    0x28282828, 0xd9d9d9d9, 0x24242424, 0xb2b2b2b2,
    0x76767676, 0x5b5b5b5b, 0xa2a2a2a2, 0x49494949,
    0x6d6d6d6d, 0x8b8b8b8b, 0xd1d1d1d1, 0x25252525,
    0x72727272, 0xf8f8f8f8, 0xf6f6f6f6, 0x64646464,
    0x86868686, 0x68686868, 0x98989898, 0x16161616,
    0xd4d4d4d4, 0xa4a4a4a4, 0x5c5c5c5c, 0xcccccccc,
    0x5d5d5d5d, 0x65656565, 0xb6b6b6b6, 0x92929292,
    0x6c6c6c6c, 0x70707070, 0x48484848, 0x50505050,
    0xfdfdfdfd, 0xedededed, 0xb9b9b9b9, 0xdadadada,
    0x5e5e5e5e, 0x15151515, 0x46464646, 0x57575757,
    0xa7a7a7a7, 0x8d8d8d8d, 0x9d9d9d9d, 0x84848484,
    0x90909090, 0xd8d8d8d8, 0xabababab, 0x00000000,
    0x8c8c8c8c, 0xbcbcbcbc, 0xd3d3d3d3, 0x0a0a0a0a,
    0xf7f7f7f7, 0xe4e4e4e4, 0x58585858, 0x05050505,
    0xb8b8b8b8, 0xb3b3b3b3, 0x45454545, 0x06060606,
    0xd0d0d0d0, 0x2c2c2c2c, 0x1e1e1e1e, 0x8f8f8f8f,
    0xcacacaca, 0x3f3f3f3f, 0x0f0f0f0f, 0x02020202,
    0xc1c1c1c1, 0xafafafaf, 0xbdbdbdbd, 0x03030303,
    0x01010101, 0x13131313, 0x8a8a8a8a, 0x6b6b6b6b,
    0x3a3a3a3a, 0x91919191, 0x11111111, 0x41414141,
    0x4f4f4f4f, 0x67676767, 0xdcdcdcdc, 0xeaeaeaea,
    0x97979797, 0xf2f2f2f2, 0xcfcfcfcf, 0xcececece,
    0xf0f0f0f0, 0xb4b4b4b4, 0xe6e6e6e6, 0x73737373,
    0x96969696, 0xacacacac, 0x74747474, 0x22222222,
    0xe7e7e7e7, 0xadadadad, 0x35353535, 0x85858585,
    0xe2e2e2e2, 0xf9f9f9f9, 0x37373737, 0xe8e8e8e8,
    0x1c1c1c1c, 0x75757575, 0xdfdfdfdf, 0x6e6e6e6e,
    0x47474747, 0xf1f1f1f1, 0x1a1a1a1a, 0x71717171,
    0x1d1d1d1d, 0x29292929, 0xc5c5c5c5, 0x89898989,
    0x6f6f6f6f, 0xb7b7b7b7, 0x62626262, 0x0e0e0e0e,
    0xaaaaaaaa, 0x18181818, 0xbebebebe, 0x1b1b1b1b,
    0xfcfcfcfc, 0x56565656, 0x3e3e3e3e, 0x4b4b4b4b,
    0xc6c6c6c6, 0xd2d2d2d2, 0x79797979, 0x20202020,
    0x9a9a9a9a, 0xdbdbdbdb, 0xc0c0c0c0, 0xfefefefe,
    0x78787878, 0xcdcdcdcd, 0x5a5a5a5a, 0xf4f4f4f4,
    0x1f1f1f1f, 0xdddddddd, 0xa8a8a8a8, 0x33333333,
    0x88888888, 0x07070707, 0xc7c7c7c7, 0x31313131,
    0xb1b1b1b1, 0x12121212, 0x10101010, 0x59595959,
    0x27272727, 0x80808080, 0xecececec, 0x5f5f5f5f,
    0x60606060, 0x51515151, 0x7f7f7f7f, 0xa9a9a9a9,
    0x19191919, 0xb5b5b5b5, 0x4a4a4a4a, 0x0d0d0d0d,
    0x2d2d2d2d, 0xe5e5e5e5, 0x7a7a7a7a, 0x9f9f9f9f,
    0x93939393, 0xc9c9c9c9, 0x9c9c9c9c, 0xefefefef,
    0xa0a0a0a0, 0xe0e0e0e0, 0x3b3b3b3b, 0x4d4d4d4d,
    0xaeaeaeae, 0x2a2a2a2a, 0xf5f5f5f5, 0xb0b0b0b0,
    0xc8c8c8c8, 0xebebebeb, 0xbbbbbbbb, 0x3c3c3c3c,
    0x83838383, 0x53535353, 0x99999999, 0x61616161,
    0x17171717, 0x2b2b2b2b, 0x04040404, 0x7e7e7e7e,
    0xbabababa, 0x77777777, 0xd6d6d6d6, 0x26262626,
    0xe1e1e1e1, 0x69696969, 0x14141414, 0x63636363,
    0x55555555, 0x21212121, 0x0c0c0c0c, 0x7d7d7d7d]
rcon = [
  0x01000000, 0x02000000, 0x04000000, 0x08000000,
  0x10000000, 0x20000000, 0x40000000, 0x80000000,
  0x1B000000, 0x36000000] #for 128-bit blocks, Rijndael never uses more than 10 rcon values
  
#Expand the cipher key into the encryption key schedule.
def AES_set_encrypt_key(userKey, bits):
  assert not userKey is None
  assert bits == 128 or bits == 192 or bits == 256
  if bits == 128: rounds = 10 #44 key dwords
  elif bits == 192: rounds = 12 #52 key dwords
  elif bits == 256: rounds = 14 #60 key dwords
  rk = [None] * ((rounds + 1) * 4)
  rk[0] = int.from_bytes(userKey[0:4], 'big')
  rk[1] = int.from_bytes(userKey[4:8], 'big')
  rk[2] = int.from_bytes(userKey[8:12], 'big')
  rk[3] = int.from_bytes(userKey[12:16], 'big')
  i, r = 0, 0
  if bits == 128:
    while True:
      temp = rk[r+3]
      rk[r+4] = (rk[r+0] ^
        (Te4[(temp >> 16) & 0xff] & 0xff000000) ^
        (Te4[(temp >>  8) & 0xff] & 0x00ff0000) ^
        (Te4[(temp      ) & 0xff] & 0x0000ff00) ^
        (Te4[(temp >> 24)       ] & 0x000000ff) ^
        rcon[i])
      rk[r+5] = rk[r+1] ^ rk[r+4]
      rk[r+6] = rk[r+2] ^ rk[r+5]
      rk[r+7] = rk[r+3] ^ rk[r+6]
      i += 1
      if i == 10: return rounds, tuple(rk)
      r += 4
  rk[4] = int.from_bytes(userKey[16:20], 'big')
  rk[5] = int.from_bytes(userKey[20:24], 'big')
  if bits == 192:
    while True:
      temp = rk[r+5]
      rk[r+6] = (rk[r+0] ^
        (Te4[(temp >> 16) & 0xff] & 0xff000000) ^
        (Te4[(temp >>  8) & 0xff] & 0x00ff0000) ^
        (Te4[(temp      ) & 0xff] & 0x0000ff00) ^
        (Te4[(temp >> 24)       ] & 0x000000ff) ^
        rcon[i])
      rk[r+7] = rk[r+1] ^ rk[r+6]
      rk[r+8] = rk[r+2] ^ rk[r+7]
      rk[r+9] = rk[r+3] ^ rk[r+8]
      i += 1
      if i == 8: return rounds, tuple(rk)
      rk[r+10] = rk[r+4] ^ rk[r+9]
      rk[r+11] = rk[r+5] ^ rk[r+10]
      r += 6
  rk[6] = int.from_bytes(userKey[24:28], 'big')
  rk[7] = int.from_bytes(userKey[28:32], 'big')
  if bits == 256:
    while True:
      temp = rk[r+7]
      rk[r+8] = (rk[r+0] ^
        (Te4[(temp >> 16) & 0xff] & 0xff000000) ^
        (Te4[(temp >>  8) & 0xff] & 0x00ff0000) ^
        (Te4[(temp      ) & 0xff] & 0x0000ff00) ^
        (Te4[(temp >> 24)       ] & 0x000000ff) ^
        rcon[i])
      rk[r+9] = rk[r+1] ^ rk[r+8]
      rk[r+10] = rk[r+2] ^ rk[r+9]
      rk[r+11] = rk[r+3] ^ rk[r+10]
      i += 1
      if i == 7: return rounds, tuple(rk)
      temp = rk[r+11]
      rk[r+12] = (rk[r+4] ^
        (Te4[(temp >> 24)       ] & 0xff000000) ^
        (Te4[(temp >> 16) & 0xff] & 0x00ff0000) ^
        (Te4[(temp >>  8) & 0xff] & 0x0000ff00) ^
        (Te4[(temp      ) & 0xff] & 0x000000ff))
      rk[r+13] = rk[r+5] ^ rk[r+12]
      rk[r+14] = rk[r+6] ^ rk[r+13]
      rk[r+15] = rk[r+7] ^ rk[r+14]
      r += 8
  return rounds, tuple(rk)
FULL_UNROLL = True
def AES_encrypt(inp, k):
  assert not k is None
  rounds, rk = k
  
  s0 = int.from_bytes(inp[0:4], 'big') ^ rk[0]
  s1 = int.from_bytes(inp[4:8], 'big') ^ rk[1]
  s2 = int.from_bytes(inp[8:12], 'big') ^ rk[2]
  s3 = int.from_bytes(inp[12:16], 'big') ^ rk[3]
  if FULL_UNROLL:    
    #round 1:
    t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[ 4]
    t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[ 5]
    t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[ 6]
    t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[ 7]
    #round 2:
    s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >>  8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[ 8]
    s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >>  8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[ 9]
    s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >>  8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[10]
    s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >>  8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[11]
    #round 3:
    t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[12]
    t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[13]
    t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[14]
    t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[15]
    #round 4:
    s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >>  8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[16]
    s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >>  8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[17]
    s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >>  8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[18]
    s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >>  8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[19]
    #round 5:
    t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[20]
    t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[21]
    t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[22]
    t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[23]
    #round 6:
    s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >>  8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[24]
    s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >>  8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[25]
    s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >>  8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[26]
    s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >>  8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[27]
    #round 7:
    t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[28]
    t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[29]
    t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[30]
    t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[31]
    #round 8:
    s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >>  8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[32]
    s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >>  8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[33]
    s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >>  8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[34]
    s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >>  8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[35]
    #round 9:
    t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[36]
    t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[37]
    t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[38]
    t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[39]
    if rounds > 10:
      #round 10:
      s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >>  8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[40]
      s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >>  8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[41]
      s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >>  8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[42]
      s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >>  8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[43]
      #round 11:
      t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[44]
      t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[45]
      t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[46]
      t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[47]
      if rounds > 12:
        #round 12:
        s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >>  8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[48]
        s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >>  8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[49]
        s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >>  8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[50]
        s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >>  8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[51]
        #round 13:
        t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >>  8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[52]
        t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >>  8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[53]
        t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >>  8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[54]
        t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >>  8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[55]
    r = rounds << 2
  else: #!FULL_UNROLL
    #Nr - 1 full rounds:
    i = rounds >> 1
    r = 0
    while True:
        t0 = (
            Te0[(s0 >> 24)       ] ^
            Te1[(s1 >> 16) & 0xff] ^
            Te2[(s2 >>  8) & 0xff] ^
            Te3[(s3      ) & 0xff] ^
            rk[r+4])
        t1 = (
            Te0[(s1 >> 24)       ] ^
            Te1[(s2 >> 16) & 0xff] ^
            Te2[(s3 >>  8) & 0xff] ^
            Te3[(s0      ) & 0xff] ^
            rk[r+5])
        t2 = (
            Te0[(s2 >> 24)       ] ^
            Te1[(s3 >> 16) & 0xff] ^
            Te2[(s0 >>  8) & 0xff] ^
            Te3[(s1      ) & 0xff] ^
            rk[r+6])
        t3 = (
            Te0[(s3 >> 24)       ] ^
            Te1[(s0 >> 16) & 0xff] ^
            Te2[(s1 >>  8) & 0xff] ^
            Te3[(s2      ) & 0xff] ^
            rk[r+7])

        r += 8
        i -= 1
        if i == 0: break

        s0 = (
            Te0[(t0 >> 24)       ] ^
            Te1[(t1 >> 16) & 0xff] ^
            Te2[(t2 >>  8) & 0xff] ^
            Te3[(t3      ) & 0xff] ^
            rk[r+0])
        s1 = (
            Te0[(t1 >> 24)       ] ^
            Te1[(t2 >> 16) & 0xff] ^
            Te2[(t3 >>  8) & 0xff] ^
            Te3[(t0      ) & 0xff] ^
            rk[r+1])
        s2 = (
            Te0[(t2 >> 24)       ] ^
            Te1[(t3 >> 16) & 0xff] ^
            Te2[(t0 >>  8) & 0xff] ^
            Te3[(t1      ) & 0xff] ^
            rk[r+2])
        s3 = (
            Te0[(t3 >> 24)       ] ^
            Te1[(t0 >> 16) & 0xff] ^
            Te2[(t1 >>  8) & 0xff] ^
            Te3[(t2      ) & 0xff] ^
            rk[r+3])

  #?FULL_UNROLL
  #apply last round and
  #map cipher state to byte array block:
  s0 = (
    (Te4[(t0 >> 24)       ] & 0xff000000) ^
    (Te4[(t1 >> 16) & 0xff] & 0x00ff0000) ^
    (Te4[(t2 >>  8) & 0xff] & 0x0000ff00) ^
    (Te4[(t3      ) & 0xff] & 0x000000ff) ^
    rk[r+0])
  s1 = (
    (Te4[(t1 >> 24)       ] & 0xff000000) ^
    (Te4[(t2 >> 16) & 0xff] & 0x00ff0000) ^
    (Te4[(t3 >>  8) & 0xff] & 0x0000ff00) ^
    (Te4[(t0      ) & 0xff] & 0x000000ff) ^
    rk[r+1])
  s2 = (
    (Te4[(t2 >> 24)       ] & 0xff000000) ^
    (Te4[(t3 >> 16) & 0xff] & 0x00ff0000) ^
    (Te4[(t0 >>  8) & 0xff] & 0x0000ff00) ^
    (Te4[(t1      ) & 0xff] & 0x000000ff) ^
    rk[r+2])
  s3 = (
    (Te4[(t3 >> 24)       ] & 0xff000000) ^
    (Te4[(t0 >> 16) & 0xff] & 0x00ff0000) ^
    (Te4[(t1 >>  8) & 0xff] & 0x0000ff00) ^
    (Te4[(t2      ) & 0xff] & 0x000000ff) ^
    rk[r+3])
  return s0.to_bytes(4, byteorder='big') + s1.to_bytes(4, byteorder='big') + s2.to_bytes(4, byteorder='big') + s3.to_bytes(4, byteorder='big')
#https://github.com/boppreh/aes/blob/master/aes.py
s_box = (
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16,
)
inv_s_box = (
    0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
    0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
    0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
    0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
    0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
    0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
    0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
    0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
    0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
    0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
    0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
    0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
    0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
    0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
    0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D,
)
r_con = (
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40,
    0x80, 0x1B, 0x36, 0x6C, 0xD8, 0xAB, 0x4D, 0x9A,
    0x2F, 0x5E, 0xBC, 0x63, 0xC6, 0x97, 0x35, 0x6A,
    0xD4, 0xB3, 0x7D, 0xFA, 0xEF, 0xC5, 0x91, 0x39,
)
def sub_bytes(s):
  for i in range(4):
    for j in range(4): s[i][j] = s_box[s[i][j]]
def inv_sub_bytes(s):
  for i in range(4):
    for j in range(4): s[i][j] = inv_s_box[s[i][j]]
def shift_rows(s):
  s[0][1], s[1][1], s[2][1], s[3][1] = s[1][1], s[2][1], s[3][1], s[0][1]
  s[0][2], s[1][2], s[2][2], s[3][2] = s[2][2], s[3][2], s[0][2], s[1][2]
  s[0][3], s[1][3], s[2][3], s[3][3] = s[3][3], s[0][3], s[1][3], s[2][3]
def inv_shift_rows(s):
  s[0][1], s[1][1], s[2][1], s[3][1] = s[3][1], s[0][1], s[1][1], s[2][1]
  s[0][2], s[1][2], s[2][2], s[3][2] = s[2][2], s[3][2], s[0][2], s[1][2]
  s[0][3], s[1][3], s[2][3], s[3][3] = s[1][3], s[2][3], s[3][3], s[0][3]
# learned from http://cs.ucsb.edu/~koc/cs178/projects/JT/aes.c
xtime = lambda a: (((a << 1) ^ 0x1B) & 0xFF) if (a & 0x80) else (a << 1)
def mix_single_column(a):
  # see Sec 4.1.2 in The Design of Rijndael
  t = a[0] ^ a[1] ^ a[2] ^ a[3]
  u = a[0]
  a[0] ^= t ^ xtime(a[0] ^ a[1])
  a[1] ^= t ^ xtime(a[1] ^ a[2])
  a[2] ^= t ^ xtime(a[2] ^ a[3])
  a[3] ^= t ^ xtime(a[3] ^ u)
def mix_columns(s):
  for i in range(4): mix_single_column(s[i])
def inv_mix_columns(s):
  # see Sec 4.1.3 in The Design of Rijndael
  for i in range(4):
    u = xtime(xtime(s[i][0] ^ s[i][2]))
    v = xtime(xtime(s[i][1] ^ s[i][3]))
    s[i][0] ^= u
    s[i][1] ^= v
    s[i][2] ^= u
    s[i][3] ^= v
  mix_columns(s)
def add_round_key(s, k):
  for i in range(4):
    for j in range(4): s[i][j] ^= k[i][j]
def AES_encrypt_no_tab(inp, k):
  rounds, rk = k
  inp = [x for x in inp]
  inpmat = [inp[0:4], inp[4:8], inp[8:12], inp[12:16]]
  rk = [[y for y in x.to_bytes(4, 'big')] for x in rk]
  add_round_key(inpmat, rk[:4])
  for i in range(1, rounds):
    sub_bytes(inpmat)
    shift_rows(inpmat)
    mix_columns(inpmat)
    add_round_key(inpmat, rk[4*i:4*i+4])
  sub_bytes(inpmat)
  shift_rows(inpmat)
  add_round_key(inpmat, rk[4*rounds:])
  return b''.join(x.to_bytes(1, 'big') for y in inpmat for x in y)
def AES_decrypt_no_tab(inp, k):
  rounds, rk = k
  inp = [x for x in inp]
  inpmat = [inp[0:4], inp[4:8], inp[8:12], inp[12:16]]
  rk = [[y for y in x.to_bytes(4, 'big')] for x in rk]
  add_round_key(inpmat, rk[4*rounds:])
  inv_shift_rows(inpmat)
  inv_sub_bytes(inpmat)
  for i in range(rounds-1, 0, -1):
    add_round_key(inpmat, rk[4*i:4*i+4])
    inv_mix_columns(inpmat)
    inv_shift_rows(inpmat)
    inv_sub_bytes(inpmat)
  add_round_key(inpmat, rk[:4])
  return b''.join(x.to_bytes(1, 'big') for y in inpmat for x in y)

#AES_decrypt can be found:
#https://github.com/openssl/openssl/blob/master/crypto/aes/aes_core.c
import virt
def save_aes_virtual(v, bits):
  op, g, inpmap, outp, subg = v
  virt.virt_to_c("aes" + str(bits), "AES_" + str(bits), op, g, 10+1, inpmap, outp, subg)
def run_aes_virtual(inp, v, ksched=None):
  op, g, inpmap, outp, subg = v
  inp = int.from_bytes(inp[0:16 if ksched is None else ksched // 8], 'little')
  accepting = virt.run_virtual(op, g, 10+1, [inpmap[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inp), 128 if ksched is None else ksched)) if x], inpmap, outp, subg)
  outv = virt.virtual_to_constant([x in accepting for x in outp])
  return outv.to_bytes(16 if ksched is None else ((ksched//32)+6+1)*4*4, byteorder='little')
def aes_virtual_encrypt(k):
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(128, node, g, op)
  return op, g, inp, aes_virtual_encrypt_no_tab(inp, round_keys_to_virtual(k[1]), k[0], node, g, op, subg), subg
def round_keys_to_virtual(rk):
  return [[virt.constant_to_virtual(y) for y in x.to_bytes(4, 'big')] for x in rk]
def aes_virtual_decrypt(k):
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(128, node, g, op)
  return op, g, inp, aes_virtual_decrypt_no_tab(inp, round_keys_to_virtual(k[1]), k[0], node, g, op, subg), subg
def aes_virtual_key_sched(bits):
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(bits, node, g, op)
  return op, g, inp, [x for y in AES_set_encrypt_key_virtual(inp, bits, node, g, op)[1] for x in y], subg
def do_aes_virtual_encrypt(inp, k, node, g, op, subg):
  assert not k is None
  rounds, rk = k
  s = inp[:]
  for ix in range(4):
    chk = int.from_bytes(rk[ix].to_bytes(4, byteorder='big'), 'little')
    for j in range(32):
      if (chk & (1 << j)) != 0:
        virt.set_bit_range(s, ix * 32 + j, ix * 32 + j+1, virt.not_to_virtual(virt.get_bit_range(s, ix * 32 + j, ix * 32 + j+1), node, g, op))
  i = rounds >> 1
  r = 0
  #the XOR of XORs could be combined if the multi xor_to_virtual combines with table_lookup_virtual
  while True:
      t = [x for y in [virt.multi_to_virtual([virt.table_lookup_virtual(virt.get_bit_range(s, byt*8, (byt+1)*8), [virt.constant_to_virtual(int.from_bytes((Te[i] ^ rk[r+ri+4] if Te == Te0 else Te[i]).to_bytes(4, byteorder='big'), 'little')) for i in range(256)], node, g, op) for Te, byt in qw], virt.xor_to_virtual, node, g, op) for ri,qw in enumerate(
             (((Te0, 0), (Te1, 5), (Te2, 10), (Te3, 15)),
                  ((Te0, 4), (Te1, 9), (Te2, 14), (Te3, 3)),
                  ((Te0, 8), (Te1, 13), (Te2, 2), (Te3, 7)),
                  ((Te0, 12), (Te1, 1), (Te2, 6), (Te3, 11))))] for x in y]
      r += 8
      i -= 1
      if i == 0: break
      s = [x for y in [virt.multi_to_virtual([virt.table_lookup_virtual(virt.get_bit_range(t, byt*8, (byt+1)*8), [virt.constant_to_virtual(int.from_bytes((Te[i] ^ rk[r+ri] if Te == Te0 else Te[i]).to_bytes(4, byteorder='big'), 'little')) for i in range(256)], node, g, op) for Te, byt in qw], virt.xor_to_virtual, node, g, op) for ri,qw in enumerate(
             (((Te0, 0), (Te1, 5), (Te2, 10), (Te3, 15)),
                  ((Te0, 4), (Te1, 9), (Te2, 14), (Te3, 3)),
                  ((Te0, 8), (Te1, 13), (Te2, 2), (Te3, 7)),
                  ((Te0, 12), (Te1, 1), (Te2, 6), (Te3, 11))))] for x in y]

  s = [x for y in [virt.table_lookup_virtual(virt.get_bit_range(t, byt*8, (byt+1)*8), [virt.constant_to_virtual((int.from_bytes((Te4[i] ^ rk[r+ri]).to_bytes(4, byteorder='big'), 'little') >> (b*8)) & 0xFF) for i in range(256)], node, g, op) for ri,qw in enumerate(
             (((0, 5, 10, 15)),
              ((4, 9, 14, 3)),
              ((8, 13, 2, 7)),
              ((12, 1, 6, 11)))) for b, byt in enumerate(qw)] for x in y]
  return s
def AES_set_encrypt_key_virtual(userKey, bits, node, g, op):
  assert bits == 128 or bits == 192 or bits == 256
  if bits == 128: rounds = 10 #44 key dwords
  elif bits == 192: rounds = 12 #52 key dwords
  elif bits == 256: rounds = 14 #60 key dwords
  rk = [None] * ((rounds + 1) * 4)
  rk[0] = virt.get_bit_range(userKey, 0, 32)
  rk[1] = virt.get_bit_range(userKey, 32, 32*2)
  rk[2] = virt.get_bit_range(userKey, 32*2, 32*3)
  rk[3] = virt.get_bit_range(userKey, 32*3, 32*4)
  i, r = 0, 0
  if bits == 128:
    while True:
      temp = rk[r+3]
      rk[r+4] = virt.multi_to_virtual([rk[r+0], [x for y in [virt.table_lookup_virtual(virt.get_bit_range(temp, byt*8, (byt+1)*8), [virt.constant_to_virtual((int.from_bytes(Te4[i].to_bytes(4, byteorder='big'), 'little') >> (b*8)) & 0xFF) for i in range(256)], node, g, op) for b, byt in enumerate((1, 2, 3, 0))] for x in y], virt.constant_to_virtual(int.from_bytes(rcon[i].to_bytes(4, byteorder='big'), 'little'))], virt.xor_to_virtual, node, g, op)
      rk[r+5] = virt.multi_to_virtual([rk[r+1], rk[r+4]], virt.xor_to_virtual, node, g, op)
      rk[r+6] = virt.multi_to_virtual([rk[r+2], rk[r+5]], virt.xor_to_virtual, node, g, op)
      rk[r+7] = virt.multi_to_virtual([rk[r+3], rk[r+6]], virt.xor_to_virtual, node, g, op)
      i += 1
      if i == 10: return rounds, tuple(rk)
      r += 4
  rk[4] = virt.get_bit_range(userKey, 32*4, 32*5)
  rk[5] = virt.get_bit_range(userKey, 32*5, 32*6)
  if bits == 192:
    while True:
      temp = rk[r+5]
      rk[r+6] = virt.multi_to_virtual([rk[r+0], [x for y in [virt.table_lookup_virtual(virt.get_bit_range(temp, byt*8, (byt+1)*8), [virt.constant_to_virtual((int.from_bytes(Te4[i].to_bytes(4, byteorder='big'), 'little') >> (b*8)) & 0xFF) for i in range(256)], node, g, op) for b, byt in enumerate((1, 2, 3, 0))] for x in y], virt.constant_to_virtual(int.from_bytes(rcon[i].to_bytes(4, byteorder='big'), 'little'))], virt.xor_to_virtual, node, g, op)
      rk[r+7] = virt.multi_to_virtual([rk[r+1], rk[r+6]], virt.xor_to_virtual, node, g, op)
      rk[r+8] = virt.multi_to_virtual([rk[r+2], rk[r+7]], virt.xor_to_virtual, node, g, op)
      rk[r+9] = virt.multi_to_virtual([rk[r+3], rk[r+8]], virt.xor_to_virtual, node, g, op)
      i += 1
      if i == 8: return rounds, tuple(rk)
      rk[r+10] = virt.multi_to_virtual([rk[r+4], rk[r+9]], virt.xor_to_virtual, node, g, op)
      rk[r+11] = virt.multi_to_virtual([rk[r+5], rk[r+10]], virt.xor_to_virtual, node, g, op)
      r += 6
  rk[6] = virt.get_bit_range(userKey, 32*6, 32*7)
  rk[7] = virt.get_bit_range(userKey, 32*7, 32*8)
  if bits == 256:
    while True:
      temp = rk[r+7]
      rk[r+8] = virt.multi_to_virtual([rk[r+0], [x for y in [virt.table_lookup_virtual(virt.get_bit_range(temp, byt*8, (byt+1)*8), [virt.constant_to_virtual((int.from_bytes(Te4[i].to_bytes(4, byteorder='big'), 'little') >> (b*8)) & 0xFF) for i in range(256)], node, g, op) for b, byt in enumerate((1, 2, 3, 0))] for x in y], virt.constant_to_virtual(int.from_bytes(rcon[i].to_bytes(4, byteorder='big'), 'little'))], virt.xor_to_virtual, node, g, op)
      rk[r+9] = virt.multi_to_virtual([rk[r+1], rk[r+8]], virt.xor_to_virtual, node, g, op)
      rk[r+10] = virt.multi_to_virtual([rk[r+2], rk[r+9]], virt.xor_to_virtual, node, g, op)
      rk[r+11] = virt.multi_to_virtual([rk[r+3], rk[r+10]], virt.xor_to_virtual, node, g, op)
      i += 1
      if i == 7: return rounds, tuple(rk)
      temp = rk[r+11]
      rk[r+12] = virt.multi_to_virtual([rk[r+4], [x for y in [virt.table_lookup_virtual(virt.get_bit_range(temp, byt*8, (byt+1)*8), [virt.constant_to_virtual((int.from_bytes(Te4[i].to_bytes(4, byteorder='big'), 'little') >> (b*8)) & 0xFF) for i in range(256)], node, g, op) for b, byt in enumerate((0, 1, 2, 3))] for x in y]], virt.xor_to_virtual, node, g, op)
      rk[r+13] = virt.multi_to_virtual([rk[r+5], rk[r+12]], virt.xor_to_virtual, node, g, op)
      rk[r+14] = virt.multi_to_virtual([rk[r+6], rk[r+13]], virt.xor_to_virtual, node, g, op)
      rk[r+15] = virt.multi_to_virtual([rk[r+7], rk[r+14]], virt.xor_to_virtual, node, g, op)
      r += 8
  return rounds, rk
def sub_bytes_virtual(s, node, g, op, subg):
  for i in range(4):
    for j in range(4):
      s[i][j] = virt.table_lookup_virtual(s[i][j], [virt.constant_to_virtual(x) for x in s_box], node, g, op, subg)
def inv_sub_bytes_virtual(s, node, g, op, subg):
  for i in range(4):
    for j in range(4):
      s[i][j] = virt.table_lookup_virtual(s[i][j], [virt.constant_to_virtual(x) for x in inv_s_box], node, g, op, subg)
# learned from http://cs.ucsb.edu/~koc/cs178/projects/JT/aes.c
def xtime_virtual(a, node, g, op):
  return virt.selection_to_virtual(virt.get_bit_range(a, -1, None), virt.multi_to_virtual([virt.constant_to_virtual(0x1B), virt.get_false() + virt.get_bit_range(a, 0, -1)], virt.xor_to_virtual, node, g, op), virt.get_false() + virt.get_bit_range(a, 0, -1), node, g, op)
def mix_single_column_virtual(a, node, g, op):
  # see Sec 4.1.2 in The Design of Rijndael
  t = virt.multi_to_virtual(a, virt.xor_to_virtual, node, g, op)
  u = a[0]
  a[0] = virt.multi_to_virtual([a[0], t, xtime_virtual(virt.multi_to_virtual([a[0], a[1]], virt.xor_to_virtual, node, g, op), node, g, op)], virt.xor_to_virtual, node, g, op)
  a[1] = virt.multi_to_virtual([a[1], t, xtime_virtual(virt.multi_to_virtual([a[1], a[2]], virt.xor_to_virtual, node, g, op), node, g, op)], virt.xor_to_virtual, node, g, op)
  a[2] = virt.multi_to_virtual([a[2], t, xtime_virtual(virt.multi_to_virtual([a[2], a[3]], virt.xor_to_virtual, node, g, op), node, g, op)], virt.xor_to_virtual, node, g, op)
  a[3] = virt.multi_to_virtual([a[3], t, xtime_virtual(virt.multi_to_virtual([a[3], u], virt.xor_to_virtual, node, g, op), node, g, op)], virt.xor_to_virtual, node, g, op)
def mix_columns_virtual(s, node, g, op):
  for i in range(4): mix_single_column_virtual(s[i], node, g, op)
def inv_mix_columns_virtual(s, node, g, op):
  # see Sec 4.1.3 in The Design of Rijndael
  for i in range(4):
    u = xtime_virtual(xtime_virtual(virt.multi_to_virtual([s[i][0], s[i][2]], virt.xor_to_virtual, node, g, op), node, g, op), node, g, op)
    v = xtime_virtual(xtime_virtual(virt.multi_to_virtual([s[i][1], s[i][3]], virt.xor_to_virtual, node, g, op), node, g, op), node, g, op)
    s[i][0] = virt.multi_to_virtual([s[i][0], u], virt.xor_to_virtual, node, g, op)
    s[i][1] = virt.multi_to_virtual([s[i][1], v], virt.xor_to_virtual, node, g, op)
    s[i][2] = virt.multi_to_virtual([s[i][2], u], virt.xor_to_virtual, node, g, op)
    s[i][3] = virt.multi_to_virtual([s[i][3], v], virt.xor_to_virtual, node, g, op)
  mix_columns_virtual(s, node, g, op)
def add_round_key_virtual(s, k, node, g, op):
  for i in range(4):
    for j in range(4):
      s[i][j] = virt.multi_to_virtual([s[i][j], k[i][j]], virt.xor_to_virtual, node, g, op)
def aes_virtual_encrypt_no_tab(inp, rk, rounds, node, g, op, subg):
  inpmat = [[virt.get_bit_range(inp, i*32, i*32+8), virt.get_bit_range(inp, i*32+8, i*32+8*2), virt.get_bit_range(inp, i*32+8*2, i*32+8*3), virt.get_bit_range(inp, i*32+8*3, i*32+8*4)] for i in range(4)]
  add_round_key_virtual(inpmat, rk[:4], node, g, op)
  for i in range(1, rounds):
    sub_bytes_virtual(inpmat, node, g, op, subg)
    shift_rows(inpmat)
    mix_columns_virtual(inpmat, node, g, op)
    add_round_key_virtual(inpmat, rk[4*i:4*i+4], node, g, op)
  sub_bytes_virtual(inpmat, node, g, op, subg)
  shift_rows(inpmat)
  add_round_key_virtual(inpmat, rk[4*rounds:], node, g, op)
  return [x for y in inpmat for z in y for x in z]
def aes_virtual_decrypt_no_tab(inp, rk, rounds, node, g, op, subg):
  inpmat = [[virt.get_bit_range(inp, i*32, i*32+8), virt.get_bit_range(inp, i*32+8, i*32+8*2), virt.get_bit_range(inp, i*32+8*2, i*32+8*3), virt.get_bit_range(inp, i*32+8*3, i*32+8*4)] for i in range(4)]
  add_round_key_virtual(inpmat, rk[4*rounds:], node, g, op)
  inv_shift_rows(inpmat)
  inv_sub_bytes_virtual(inpmat, node, g, op, subg)
  for i in range(rounds-1, 0, -1):
    add_round_key_virtual(inpmat, rk[4*i:4*i+4], node, g, op)
    inv_mix_columns_virtual(inpmat, node, g, op)
    inv_shift_rows(inpmat)
    inv_sub_bytes_virtual(inpmat, node, g, op, subg)
  add_round_key_virtual(inpmat, rk[:4], node, g, op)
  return [x for y in inpmat for z in y for x in z]
def aes_virtual_encrypt_const_subg(num, aeskey, node, g, op, subg):
  rounds, rk = AES_set_encrypt_key(aeskey, len(aeskey)*8)
  return aes_virtual_encrypt_no_tab(num, round_keys_to_virtual(rk), rounds, node, g, op, subg)
def aes_virtual_decrypt_const_subg(num, aeskey, node, g, op, subg):
  rounds, rk = AES_set_encrypt_key(aeskey, len(aeskey)*8)
  return aes_virtual_decrypt_no_tab(num, round_keys_to_virtual(rk), rounds, node, g, op, subg)
def aes_virtual_encrypt_subg(num, rounds, node, g, op, subg):
  return aes_virtual_encrypt_no_tab(virt.get_bit_range(num, 0, 128), [[virt.get_bit_range(num, 128+i*16+j*4, 128+i*16+(j+1)*4) for j in range(4)] for i in range((rounds+1)*4)], rounds, node, g, op, subg)
def aes_virtual_decrypt_subg(num, rounds, node, g, op, subg):
  return aes_virtual_decrypt_no_tab(virt.get_bit_range(num, 0, 128), [[virt.get_bit_range(num, 128+i*16+j*4, 128+i*16+(j+1)*4) for j in range(4)] for i in range((rounds+1)*4)], rounds, node, g, op, subg)
def aes_encrypt_subg(blocks, aeskey):
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(blocks * 128, node, g, op)
  outp = []
  for x in range(blocks):
    outp += virt.subg_virtual(aes_virtual_encrypt_const_subg, virt.get_bit_range(inp, x*128, (x+1)*128), (aeskey,), node, g, op, subg, True)
  return op, g, inp, outp, subg
def run_aes_virtual_subg(inp, v, blocks):
  op, g, inpmap, outp, subg = v
  inp = int.from_bytes(inp[0:16*blocks], 'little')
  accepting = virt.run_virtual(op, g, 10+1, [inpmap[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inp), 128*blocks)) if x], inpmap, outp, subg)
  outv = virt.virtual_to_constant([x in accepting for x in outp])
  return outv.to_bytes(16*blocks, byteorder='little')

#https://whibox.io/contests/2021/ CHES 2021 White Box ECDSA

#SageMath source code: https://github.com/sagemath/sage
#SageMath Windows binaries: https://github.com/sagemath/sage-windows/releases
#SageMath documentation: https://doc.sagemath.org/html/en/reference/index.html

#pycryptodome (replaces pycrypto), pip install pycryptodome
import os
from Crypto import Random
from Crypto.Cipher import AES
def pad(s):
  return s + bytes((AES.block_size - len(s) % AES.block_size) * [AES.block_size - len(s) % AES.block_size])
def unpad(s):
  return s[:-ord(s[len(s)-1:])]
def aes_encrypt(data, key, pad=False):
  if pad: data = pad(data)
  cipher = AES.new(key, AES.MODE_ECB)
  return cipher.encrypt(data)
def aes_decrypt(data, key, pad=False):
  cipher = AES.new(key, AES.MODE_ECB)
  if pad: return unpad(cipher.decrypt(data))
  else: return cipher.decrypt(data)
def dimacs_to_clause(cnffile):
  clauses = []
  with open(cnffile, "r") as f:
    lines = f.readlines() #p cnf <number variables> <number clauses>
    for line in lines[1:]:
      clauses.append(tuple([int(x) for x in line.strip().split(" ")[:-1]]))
  return clauses
def map_to_vars(mapfile):
  d = {}
  with open(mapfile, "r") as f:
    for line in f.readlines():
      kv = line.split(" ")
      d[kv[0]] = int(kv[1].strip())
  return d
import sat
def sat_unit_prop(cnf):
  clauses = {frozenset(c) for c in cnf}
  map = sat.getsatmap(clauses)
  while True:
    s = sat.unit_prop(clauses, map)
    if len(s) == 0: break
    sat.pure_literal(clauses, map)
    print(len(s))
  return clauses, map
def all_vars(cnf):
  return {y if y > 0 else -y for x in cnf for y in x}
sbox = (99, 124, 119, 123, 242, 107, 111, 197, 48, 1, 103, 43, 254, 215, 171, 118, 202, 130, 201, 125, 250, 89, 71, 240, 173, 212, 162, 175, 156, 164, 114, 192, 183, 253, 147, 38, 54, 63, 247, 204, 52, 165, 229, 241, 113, 216, 49, 21, 4, 199, 35, 195, 24, 150, 5, 154, 7, 18, 128, 226, 235, 39, 178, 117, 9, 131, 44, 26, 27, 110, 90, 160, 82, 59, 214, 179, 41, 227, 47, 132, 83, 209, 0, 237, 32, 252, 177, 91, 106, 203, 190, 57, 74, 76, 88, 207, 208, 239, 170, 251, 67, 77, 51, 133, 69, 249, 2, 127, 80, 60, 159, 168, 81, 163, 64, 143, 146, 157, 56, 245, 188, 182, 218, 33, 16, 255, 243, 210, 205, 12, 19, 236, 95, 151, 68, 23, 196, 167, 126, 61, 100, 93, 25, 115, 96, 129, 79, 220, 34, 42, 144, 136, 70, 238, 184, 20, 222, 94, 11, 219, 224, 50, 58, 10, 73, 6, 36, 92, 194, 211, 172, 98, 145, 149, 228, 121, 231, 200, 55, 109, 141, 213, 78, 169, 108, 86, 244, 234, 101, 122, 174, 8, 186, 120, 37, 46, 28, 166, 180, 198, 232, 221, 116, 31, 75, 189, 139, 138, 112, 62, 181, 102, 72, 3, 246, 14, 97, 53, 87, 185, 134, 193, 29, 158, 225, 248, 152, 17, 105, 217, 142, 148, 155, 30, 135, 233, 206, 85, 40, 223, 140, 161, 137, 13, 191, 230, 66, 104, 65, 153, 45, 15, 176, 84, 187, 22)
def aes_stamp_key(key):
  cnf = dimacs_to_clause(os.path.join("results", "AES_cnf.txt"))
  mapvars = map_to_vars(os.path.join("results", "AES_map.txt"))
  allsatvar = aes_sat(b'\x00'*16, key, True)
  init = []
  for mv in mapvars:
    if mv.startswith('k') or mv.startswith('s'):
      init.append((mapvars[mv] if mapvars[mv] in allsatvar else -mapvars[mv],))
  """
  keynum = int.from_bytes(key, 'big')
  for round in range(8):
    for bit in range(16):
      keyn = mapvars["k00" + "%02d" % bit + "%02d" % round]
      init.append((keyn if (1 << (127 - (bit * 8 + round))) & keynum != 0 else -keyn,))
  """
  #from pysat.solvers import Glucose3
  #g = Glucose3(bootstrap_with=cnf)
  #valid, prop = g.propagate(assumptions=[x[0] for x in init])
  #print(valid, len(prop), len(init))
  clauses, map = sat_unit_prop(cnf + init)
  #print(len(all_vars(cnf)), len(all_vars(clauses)))
  #assert False
  from pysat.solvers import Glucose3
  with open(os.path.join("results", "AES_cnf_stamp.txt"), "w", newline='') as f:
    f.write("p cnf " + str(len(all_vars(clauses))) + " " + str(len(clauses)) + "\n")
    for clause in clauses: f.write(" ".join(str(x) for x in sorted(clause, key=lambda y: abs(y))) + " 0\n")
def aes_stamped_sat(input):
  cnf = dimacs_to_clause(os.path.join("results", "AES_cnf_stamp.txt"))
  mapvars = map_to_vars(os.path.join("results", "AES_map.txt"))
  init = []
  inputnum = int.from_bytes(input, 'big')
  for round in range(8):
    for bit in range(16):
      inpn = mapvars["P00" + "%02d" % bit + "%02d" % round]
      init.append((inpn if (1 << (127 - (bit * 8 + round))) & inputnum != 0 else -inpn,))
  print(len(all_vars(cnf)), len(cnf)+len(init))
  for sol in sat.pycryptosat(cnf + init):
    solset = set(sol)
    outnum = 0
    for round in range(8):
      for bit in range(16):
        outn = mapvars["C10" + "%02d" % bit + "%02d" % round]
        if outn in solset: outnum |= (1 << (127 - (bit * 8 + round)))
    return outnum.to_bytes(16, byteorder='big')
def aes_sat(input, key, allsatvar=False):
  cnf = dimacs_to_clause(os.path.join("results", "AES_cnf.txt"))
  mapvars = map_to_vars(os.path.join("results", "AES_map.txt"))
  init = []
  inputnum = int.from_bytes(input, 'big')
  keynum = int.from_bytes(key, 'big')
  for round in range(8):
    for bit in range(16):
      inpn = mapvars["P00" + "%02d" % bit + "%02d" % round]
      init.append((inpn if (1 << (127 - (bit * 8 + round))) & inputnum != 0 else -inpn,))
      keyn = mapvars["k00" + "%02d" % bit + "%02d" % round]
      init.append((keyn if (1 << (127 - (bit * 8 + round))) & keynum != 0 else -keyn,))
  print(len(all_vars(cnf)), len(cnf)+len(init))
  for sol in sat.pycryptosat(cnf + init):
    solset = set(sol)
    if allsatvar: return solset
    outnum = 0
    """
    alls = []
    for round in range(10):
      for row in range(4):
        for sbox in range(8):
          s = "s" + "%01d" % round + "%01d" % row + "%01d" % sbox
          alls.append(s if mapvars[s] in solset else "-" + s)
    print(",".join(alls))
    """
    for round in range(8):
      for bit in range(16):
        outn = mapvars["C10" + "%02d" % bit + "%02d" % round]
        if outn in solset: outnum |= (1 << (127 - (bit * 8 + round)))
    return outnum.to_bytes(16, byteorder='big')
def test_aes(bits):
  #print(AES.block_size) #AES128 is 16 byte block size and thereby key size
  #key = Random.new().read(AES.block_size) #*2
  key = b'\x12' * (bits // 8) #b'\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c\x0c'
  key = b'abcdefghijklmnopqrstuvwxyz012345'[:bits//8]
  #key192 = b'\x0c' * 24
  #key256 = b'\x0c' * 32
  data = b'Hello world!!!!\x00' + b'0123456701234567'
  enc = aes_encrypt(data, key)
  #print(enc)
  #print(aes_decrypt(enc, key))
  k = AES_set_encrypt_key(key, bits)
  assert enc[:16] == AES_encrypt_no_tab(data[:16], k)
  assert data[:16] == AES_decrypt_no_tab(enc[:16], k)
  vk = aes_virtual_key_sched(bits)
  assert b''.join([z.to_bytes(4, 'big') for z in k[1]]) == run_aes_virtual(key, vk, ksched=bits), (b''.join([z.to_bytes(4, 'big') for z in k[1]]), run_aes_virtual(key, vk, ksched=bits))
  #print(k)
  #print(k, len(k))
  #print(b''.join(x.to_bytes(4, byteorder='big') for x in k[1]))
  #print(AES_set_encrypt_key(key192, 192))
  #print(AES_set_encrypt_key(key256, 256))
  v = aes_virtual_encrypt(k)
  assert AES_encrypt(data[:16], k) == run_aes_virtual(data[:16], v)
  assert aes_decrypt(enc[:16], key) == run_aes_virtual(enc[:16], aes_virtual_decrypt(k))
  assert AES_encrypt(data[:16], k) + AES_encrypt(data[16:], k) == run_aes_virtual(data[:16], v) + run_aes_virtual(data[16:], aes_virtual_encrypt(k))
  vs = aes_encrypt_subg(2, key)
  assert AES_encrypt(data[:16], k) + AES_encrypt(data[16:], k) == run_aes_virtual_subg(data, vs, 2), (AES_encrypt(data[:16], k) + AES_encrypt(data[16:], k), run_aes_virtual_subg(data, vs, 2))
  #aes_stamp_key(key)
  #print(aes_stamped_sat(data))
  #print(aes_sat(data, key))
def gen_aes(bits):
  key = b'\x12' * (bits // 8)
  k = AES_set_encrypt_key(key, bits)
  v = aes_virtual_encrypt(k)
  save_aes_virtual(v, bits)
test_aes(128)
test_aes(192)
test_aes(256)
gen_aes(128)
gen_aes(192)
gen_aes(256)
#SAW: Software Analysis Workbench https://saw.galois.com/
"""

aesEncryptBit1 x = (aesEncrypt x) @ 0


m <- cryptol_load "AES.cry";
t <- cryptol_extract m "aesEncryptBit1";
write_cnf "aes.cnf" t;

"""