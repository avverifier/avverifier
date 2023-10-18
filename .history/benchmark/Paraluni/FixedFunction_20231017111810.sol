    mapping(address => bool) whitelist;
    
    
    function depositByAddLiquidity(uint256 _pid, address[2] memory _tokens, uint256[2] memory _amounts) external{
        require(_amounts[0] > 0 && _amounts[1] > 0, "!0");
        require(whitelist[_tokens[0]], "not access token!");
        require(whitelist[_tokens[1]], "not access token!");
        address[2] memory tokens;
        uint256[2] memory amounts;
        (tokens[0], amounts[0]) = _doTransferIn(msg.sender, _tokens[0], _amounts[0]);
        (tokens[1], amounts[1]) = _doTransferIn(msg.sender, _tokens[1], _amounts[1]);
        depositByAddLiquidityInternal(msg.sender, _pid, tokens,amounts);
    }