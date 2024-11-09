contract C {
	constructor() payable {
		require(msg.value > 100);
	}
	function f(address payable _a, uint _v) public {
		require(_v < 10);
		_a.transfer(_v);
	}
	function inv() public view {
		assert(address(this).balance > 0); // should fail
		assert(address(this).balance > 80); // should fail
		assert(address(this).balance > 90); // should fail
	}
}
// ====
// SMTEngine: all
// SMTIgnoreCex: yes
// SMTIgnoreOS: macos
// ----
// Warning 8656: (141-156): CHC: Insufficient funds happens here.
// Warning 6328: (193-226): CHC: Assertion violation happens here.
// Warning 6328: (245-279): CHC: Assertion violation happens here.
// Warning 6328: (298-332): CHC: Assertion violation happens here.
