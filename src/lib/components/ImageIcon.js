import React from 'react';
import PropTypes from 'prop-types';

function SvgImage({ fill, fillOpacity, ...props }) {
  return (
    <svg width='1em' height='1em' viewBox='0 0 58 46' fill='none' {...props}>
      <path
        d='M57 0H1a1 1 0 00-1 1v44a1 1 0 001 1h56a1 1 0 001-1V1a1 1 0 00-1-1zm-1 44H2V2h54v42z'
        fill={fill}
        fillOpacity={fillOpacity}
      />
      <path
        d='M16 22.138a5.575 5.575 0 005.57-5.568A5.575 5.575 0 0016 11a5.575 5.575 0 00-5.569 5.569 5.575 5.575 0 005.57 5.569zM16 13a3.574 3.574 0 013.57 3.569A3.574 3.574 0 0116 20.138a3.573 3.573 0 01-3.569-3.568 3.574 3.574 0 013.57-3.57zM7 40c.234 0 .47-.082.66-.25L23.973 25.39l10.302 10.3a.999.999 0 101.414-1.413l-4.807-4.807 9.181-10.054 11.261 10.323a1 1 0 001.351-1.475l-12-11a1.031 1.031 0 00-.72-.262 1.002 1.002 0 00-.694.325l-9.794 10.727-4.743-4.743a1 1 0 00-1.368-.044L6.339 38.249A1 1 0 007 39.999z'
        fill={fill}
        fillOpacity={fillOpacity}
      />
    </svg>
  );
}

SvgImage.propTypes = {
  fill: PropTypes.string,
  fillOpacity: PropTypes.number
};

SvgImage.defaultProps = {
  fill: '#fff',
  fillOpacity: 0.6
};

export default SvgImage;
