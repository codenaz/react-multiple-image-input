import styled from 'styled-components';
import FlexBox from './FlexBox';

const ImageBox = styled(FlexBox)`
  background: ${props => props.theme.colors.background};
  border: 2px solid ${props => props.theme.colors.outlineColor};
  flex-direction: row;
  justify-content: flex-start;
  padding: 1.5rem 2rem;
  margin-bottom: 1rem;
`;

export default ImageBox;
