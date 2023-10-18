    function migrateStake(address oldStaking, uint256 amount) external {
        require(oldStakingld == 0x0941A9803f3569822371C2128956daA40c985020);
        StaxLPStaking(oldStaking).migrateWithdraw(msg.sender, amount);
        _applyStake(msg.sender, amount);
    }